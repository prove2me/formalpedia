-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_B_1_mktp_variant
-- name    : ContractionLemma.Supplement.theorem_B_1_mktp_variant
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:31:28.32854+00:00
-- url     : https://prove2.me/theorems/e13bddca-7b3f-4757-bc52-d0ab566174ac
-- title:
--   Theorem B.1, p.103 — $r$-query descriptions with $|d|+t\le\theta$: decide, count and find in time $\mathrm{poly}(N+\theta)E(\theta+N2^r)$
-- statement:
--   Let $U$ be a fixed deterministic machine with random access to an oracle string $d$. Given $x\in\{0,1\}^N$, a threshold $\theta$ and a query bound $r$ with $2^r\le N$, each of the following can be computed deterministically in time $\mathrm{poly}(N+\theta)\,E(\theta+N2^r)$ and polynomial space:
--
--   1. whether $x$ has an $r$-query description $(d,t)$ with $|d|+t\le\theta$;
--   2. the number of such descriptions;
--   3. one such description, or the report that there is none.
--
--   For $\theta=O(N)$ this is $E(N)$ for constant $r$, and $2^{o(N)}$ whenever $2^r=o(\sqrt{\log N})$. A negative answer excludes only descriptions that make at most $r$ queries, so this is not an algorithm for MKTP itself.
--
--   Differences from the source:
--   - generalization: a fixed universal machine $U$ → every fixed deterministic local oracle machine $U$; reason: the proof never uses universality; a universal $U$ is a special case
--   - reading: "$U$ queries at most $r$ positions of $d$ on each input" → the $t$-step run on each input $(i,b)$ makes at most $r$ oracle steps; reason: the proof counts queries ("requests query $r+1$")
--   - reading: no space bound in the theorem sentence → space at most $C(L+1)^C$ (polynomial in the input length); reason: the paper's convention, p.3: "all algorithms are deterministic and use polynomial space unless we say otherwise"
--   - encoding: "$2^{o(N)}$ whenever $2^r=o(\sqrt{\log N})$"; random access to $d$ → time $2^{g(N)}$ with $g(N)/N\to0$ for every $r(N)$ with $2^{r(N)}/\sqrt{\log_2(N+2)}\to0$; an oracle step on a binary address, out-of-range addresses answering $0$; reason: explicit functions for $o(\cdot)$; p.103: "Out-of-range addresses have a fixed answer"
--   - encoding: $O(\cdot)$, $\mathrm{poly}(\cdot)$, $E(u)=2^{O(u/\sqrt{\log u})}$ → explicit constants fixed before the instance; $E(u)=2^{C f(u)}$, $f(u)=u/\sqrt{\log_2(u+2)}$; reason: the paper's own $f$ (p.16); log base two
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem B.1 and App. B.2, p.103

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_LocalMachine
import Definitions.Def_ContractionLemma_Supplement_Quantum
import Definitions.Def_ContractionLemma_Supplement_Classes

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem B.1 (A variant of MKTP)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.103 (PDF p.106).

"Given `x ∈ {0,1}^N`, a threshold `θ` and a query bound `r` with `2^r ≤ N`, one can decide whether
`x` has an `r`-query description with `|d| + t ≤ θ`, count such descriptions, and find one, in time
`poly(N + θ) E(θ + N 2^r)`. For `θ = O(N)` this is `E(N)` for constant `r`, and `2^{o(N)}` whenever
`2^r = o(√log N)`."

For every deterministic B.2 machine `U` and each of the three tasks (`B1Answer`: decide, count,
find) there are a machine `A` and a constant `C` such that, on every `(x, θ, r)` with `2^r ≤ N = |x|`,
`A` outputs an admissible answer in time `C (N+θ+1)^C 2^{C f(θ + N 2^r)}` and space `C (N+θ+1)^C`;
moreover, for every `c` and every fixed `r₀`, `A` runs in time `C' 2^{C' f(N)}` when `θ ≤ c N` and
`r = r₀`; and for every `c` and every `r(N)` with `2^{r(N)}/√log₂(N+2) → 0`, `A` runs in time
`2^{g(N)}` with `g(N)/N → 0` when `θ ≤ c N` and `r = r(N)`.

**Formalization Note.** `U` is a deterministic local oracle machine whose oracle answers a binary
address with the bit of `d` there (`0` out of range, declared). The paper fixes a universal `U`; its
proof never uses universality, so the theorem is stated for every such `U` (a generalization). "At
most `r` queries on each input" counts the oracle steps of the `t`-step run. `f(u) = u/√log₂(u+2)`. -/
theorem theorem_B_1_mktp_variant (p : LocalParams) (U : LProgram p) (hU : U.IsDet) (task : Fin 3) :
    ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ),
      (∀ (x : List Bool) (θ r : ℕ), 2 ^ r ≤ x.length → ∃ y, B1Answer U x θ r task y ∧
        ContractionLemma.RunsWithin A out (b1Input x θ r) y
          (C * ((x.length : ℝ) + θ + 1) ^ C * (2 : ℝ) ^ (C * fScale (θ + x.length * 2 ^ r)))
          (C * ((x.length : ℝ) + θ + 1) ^ C)) ∧
      (∀ (c r₀ : ℕ), ∃ C' : ℕ, ∀ (x : List Bool) (θ : ℕ), 2 ^ r₀ ≤ x.length → θ ≤ c * x.length →
        ∃ y, B1Answer U x θ r₀ task y ∧
          RunsInTime A out (b1Input x θ r₀) y (C' * (2 : ℝ) ^ (C' * fScale x.length))) ∧
      (∀ (c : ℕ) (rf : ℕ → ℕ),
        Filter.Tendsto (fun N : ℕ => (2 : ℝ) ^ rf N / Real.sqrt (Real.logb 2 (N + 2)))
          Filter.atTop (nhds 0) →
        ∃ g : ℕ → ℝ, Filter.Tendsto (fun N : ℕ => g N / N) Filter.atTop (nhds 0) ∧
          ∀ (x : List Bool) (θ : ℕ), 2 ^ rf x.length ≤ x.length → θ ≤ c * x.length →
            ∃ y, B1Answer U x θ (rf x.length) task y ∧
              RunsInTime A out (b1Input x θ (rf x.length)) y ((2 : ℝ) ^ g x.length)) := by sorry

end ContractionLemma.Supplement
