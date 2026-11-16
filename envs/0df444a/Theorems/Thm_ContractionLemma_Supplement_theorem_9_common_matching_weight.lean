-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_9_common_matching_weight
-- name    : ContractionLemma.Supplement.theorem_9_common_matching_weight
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:25:25.400791+00:00
-- url     : https://prove2.me/theorems/576afa50-d916-4ee5-b0e9-a3ff966b847f
-- title:
--   Theorem 9, p.33 — Common Matching Weight with sparse row supports in time $\mathrm{poly}(L+N)2^{O_c(N\sqrt{\log N})}$
-- statement:
--   Let $A\in\mathbb N^{a\times a}$ and $B\in\mathbb N^{b\times b}$, $N=2a+2b$, and let the support of a row be the set of binary positions that are nonzero in some entry of the row.
--
--   1. Fix $c\ge1$. On instances in which every row support has size at most $c\log(N+2)$, the number of pairs $(\pi,\sigma)$ of permutations with
--   $$
--   \sum_i A_{i,\pi(i)}=\sum_j B_{j,\sigma(j)},
--   $$
--   and hence feasibility, can be computed deterministically in time $\mathrm{poly}(L+N)\,2^{O_c(N\sqrt{\log N})}$ and polynomial space.
--   2. For some fixed $c\ge1$, this class contains the instances on which Common Matching Weight requires time $2^{\Omega(N\log N)}$ under ETH: if ETH holds, then for every $g$ with $g(N)=o(N\log N)$ no algorithm decides feasibility on these instances in time $2^{g(N)}\,\mathrm{poly}(L)$.
--
--   Exhaustive search takes time $2^{\Theta(N\log N)}$; part 1 is below it, and part 2 says the sparsity condition does not make the problem easy.
--
--   Differences from the source:
--   - reading: "requires time $2^{\Omega(N\log N)}$ under ETH [Soc15]" → under ETH, no algorithm decides feasibility on the class in time $C\,2^{g(N)}(L+1)^C$ for any $g$ with $g(N)/(N\log_2(N+2))\to0$; reason: the form proved on pp.34–35 ("an algorithm running in time $2^{o(N\log N)}\mathrm{poly}(L)$ … contrary to ETH")
--   - reading: no space bound in the theorem sentence → space at most $C(L+1)^C$ (polynomial in the input length); reason: the paper's convention, p.3: "all algorithms are deterministic and use polynomial space unless we say otherwise"
--   - encoding: $O(\cdot)$, $\mathrm{poly}(\cdot)$, $E(u)=2^{O(u/\sqrt{\log u})}$ → explicit constants fixed before the instance; $E(u)=2^{C f(u)}$, $f(u)=u/\sqrt{\log_2(u+2)}$; reason: the paper's own $f$ (p.16); log base two
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 9, p.33 (stated first on p.7); ETH-hard instances, pp.34–35; ETH, App. A.7, p.78

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_Problems

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem 9 (Common Matching Weight)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.33 (PDF p.36; stated first on p.7).

"Fix `c ≥ 1`. On instances in which every row support has size at most `c log(N + 2)`, the number of
pairs `(π, σ)` with `∑_i A_{i,π(i)} = ∑_j B_{j,σ(j)}`, and hence feasibility, can be computed in time
`poly(L + N) 2^{O_c(N√log N)}`. For some fixed `c`, this class contains the instances on which Common
Matching Weight requires time `2^{Ω(N log N)}` under ETH [Soc15]."

1. For every real `c ≥ 1` there are machines and a constant `C` that output, on every instance whose
   row supports have size at most `c·log₂(N+2)`, the number of such pairs, respectively whether one
   exists, in time `C (L+N+1)^C 2^{C N √log₂(N+2)}` and space `C (L+N+1)^C`.
2. There is a real `c ≥ 1` such that, under ETH, for every `g` with `g(N)/(N log₂(N+2)) → 0` no
   algorithm decides feasibility on all instances of that class in time `C 2^{g(N)} (L+1)^C`.

**Formalization Note.** `N = 2a + 2b`, `L` is the length of the encoding (entries in binary). ETH is
the supplement's `ETH` (App. A.7, p.78), the same as in Theorem A.19. "Requires time
`2^{Ω(N log N)}`" is read as "has no algorithm of time `2^{o(N log N)} poly(L)`". The
polynomial-space clause of part 1 is the paper's convention (p.3). -/
theorem theorem_9_common_matching_weight :
    (∀ c : ℝ, 1 ≤ c →
      (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ I : CMWInst, I.SparseRows c →
        ContractionLemma.RunsWithin A out I.encode (countWord I.count)
          (C * ((I.encode.length : ℝ) + I.N + 1) ^ C *
            (2 : ℝ) ^ (C * I.N * Real.sqrt (Real.logb 2 (I.N + 2))))
          (C * ((I.encode.length : ℝ) + I.N + 1) ^ C)) ∧
      (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ I : CMWInst, I.SparseRows c →
        ContractionLemma.RunsWithin A out I.encode [decide (0 < I.count)]
          (C * ((I.encode.length : ℝ) + I.N + 1) ^ C *
            (2 : ℝ) ^ (C * I.N * Real.sqrt (Real.logb 2 (I.N + 2))))
          (C * ((I.encode.length : ℝ) + I.N + 1) ^ C))) ∧
    ∃ c : ℝ, 1 ≤ c ∧ (ETH → ∀ g : ℕ → ℝ,
      Filter.Tendsto (fun N : ℕ => g N / (N * Real.logb 2 (N + 2))) Filter.atTop (nhds 0) →
      ¬ ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ I : CMWInst, I.SparseRows c →
        RunsInTime A out I.encode [decide (0 < I.count)]
          (C * (2 : ℝ) ^ g I.N * ((I.encode.length : ℝ) + 1) ^ C)) := by sorry

end ContractionLemma.Supplement
