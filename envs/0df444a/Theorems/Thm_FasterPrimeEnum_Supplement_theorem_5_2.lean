-- Prove2me | Theorems.Thm_FasterPrimeEnum_Supplement_theorem_5_2
-- name    : FasterPrimeEnum.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:52:38.130073+00:00
-- url     : https://prove2.me/theorems/8a332316-41d5-4e40-bbf9-16d5bcf8ec3d
-- title:
--   Theorem 5.2 — compression: $\kappa(a)$ in time $O(T\log T\cdot C^*(T))+R(\log T)^{2+o(1)}$
-- statement:
--   Let $T$ and $R\le T/2$ be positive integers and $\kappa:\mathbb F_2^T\to\mathbb F_2^S$ the compression map of §5.1, for a fixed irreducible $h$ of degree $\lambda=\mathrm{lg}(T+1)$ and a fixed generator $\beta$. Fix a multiplication algorithm (with (4.2)) and a transform scheme with $T(n)\ll M(n)$, and put $C^*(n)=M^*(n)+K^*(n)$. Then, given $a\in\mathbb F_2^T$, one may evaluate $\kappa(a)$ in time
--
--   $$
--   O\big(T\log T\cdot C^*(T)\big)+R(\log T)^{2+o(1)},
--   $$
--
--   after a precomputation depending only on $T$ and $R$ of cost $T(\log T)^{3+o(1)}$.
--
--   This is the compression step of the core algorithm, applied once to each interval of length $T$.
--
--   **Formalization Note** Two machines — the precomputation (input $T,R$) and the main algorithm (input $T,R$, the precomputed word and $a$) — the choice of $(h,\beta)$ for each $T$, two functions $\varepsilon_1,\varepsilon_2\to0$ of $T$ and a constant $K$ are fixed before $T,R$.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) with RunsWithin / RunOutcome (a halted run within the time bound, with exactly the output on a designated tape); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a change of the O-constant or a shift of an o(1) exponent); an existential over the more restricted machine is the stronger statement
--   - reading: the algorithms fixed in §4.1, §4.3 ("we fix …") with the standing assumption (4.2) M(kn) ≪_k M(n) (p.19) → the statement holds for every multiplication algorithm Mul with Mul.Assumption42 and every transform scheme with T(n) ≤ c·M(n); reason: the paper fixes arbitrary such algorithms and assumes (4.2) for the rest of the paper (pp.19, 27, 36); a universal quantifier is exactly "for the fixed ones, whichever they are"
--   - reading: κ(a) for the fixed h and β of §5.1, which the algorithm computes (Lemmas 4.5, 4.7) → a function fd : ℕ → FieldData chosen with the machines, with IsFieldData (lam T) (fd T) for every valid T, and the output is kappa (fd T) T R a; reason: the paper's h and β depend only on λ = lg(T + 1) and are computed by the algorithm; the existential lets the algorithm choose them, as it does
--   - encoding: a precomputation (depending only on T and R) followed by the evaluation of κ(a) → a precomputation machine P on input (T, R) halting with a word pre, and a machine A on input (T, R, pre, a); reason: this is the two-phase reading of "after a precomputation"; the precomputed data is passed as a word
--   - encoding: the two o(1) terms → two functions ε₁, ε₂ : ℕ → ℝ of T tending to 0; reason: both o(1) are as T → ∞ (they come from M(n) < n(log n)^{1+o(1)} and λ ≪ log T, p.36)
--   - encoding: log x and log log x in complexity bounds → logU x = log max(x, 2) and logU (logU x); reason: the paper's convention (p.2): in complexity bounds log x should be read as log max(x, 2)
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 5.2, p.36; §5.1, pp.35–36

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_FasterPrimeEnum_Supplement_MulAlgorithm
import Definitions.Def_FasterPrimeEnum_Supplement_TransformScheme
import Definitions.Def_FasterPrimeEnum_Supplement_kappa

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open ThreeSumApsp
open Filter Topology

/-- **Theorem 5.2 (Compression)** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851
(held version, sha256 7fc13f17…), p.36.

"Given a ∈ F₂^T, we may evaluate κ(a) ∈ F₂^S in time (5.3) O(T log T · C*(T)) + R(log T)^{2+o(1)},
after a precomputation (depending only on T and R) of cost T(log T)^{3+o(1)}."

Setting (§5.1–5.2, pp.35–36): `T` and `R ⩽ T/2` positive integers, `λ = lg(T + 1)`, `h`, `β` and
`κ : F₂^T → F₂^S` as in §5.1; "For the rest of Section 5 we fix a transform scheme (see Section 4.3)
with associated cost functions K(n) and T(n) ≪ M(n). For convenience we define C*(n) := M*(n) + K*(n)."

**Formalization Note.** Relative to every multiplication algorithm with (4.2) and every transform
scheme with `T(n) ≤ c M(n)`: there are two machines — the precomputation `P` (input: the binary
words of `T, R`) and the main algorithm `A` (input: `T, R`, the precomputed word and `a`) — a choice
of the field data `(h, β)` for each `T` (as the algorithm computes them, p.35), functions
`ε₁, ε₂ → 0` (the two `o(1)`, functions of `T`) and a constant `K`, all chosen before `T, R`. For
every valid `T, R` the precomputation halts with some word `pre` within `T (log T)^{3+ε₂(T)}`
steps, and for every `a ∈ F₂^T` (a list of `T` bits) the main algorithm halts with `κ(a)` within
`K T log T C*(T) + R (log T)^{2+ε₁(T)}` steps. Logarithms are clipped (p.2). -/
theorem theorem_5_2 (Mul : MulAlgorithm) (hMul : Mul.Assumption42) (TS : TransformScheme)
    (hT : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → TS.Tcost n ≤ c * Mul.Mcost n) :
    ∃ (P : PrimitiveMachine) (pout : Fin P.tapeCount) (A : PrimitiveMachine) (out : Fin A.tapeCount)
      (fd : ℕ → FieldData) (ε₁ ε₂ : ℕ → ℝ) (K : ℝ),
      Tendsto ε₁ atTop (𝓝 0) ∧ Tendsto ε₂ atTop (𝓝 0) ∧ 0 < K ∧
      ∀ T R : ℕ, 0 < T → 0 < R → 2 * R ≤ T →
        IsFieldData (lam T) (fd T) ∧
        ∃ pre : List Bool,
          RunsWithin P pout (Encoding.encodeList id [binWord T, binWord R]) pre
            ((T : ℝ) * logU (T : ℝ) ^ (3 + ε₂ T)) ∧
          ∀ a : List Bool, a.length = T →
            RunsWithin A out (Encoding.encodeList id [binWord T, binWord R, pre, a])
              (kappa (fd T) T R a)
              (K * (T : ℝ) * logU (T : ℝ) * Cstar Mul TS T +
                (R : ℝ) * logU (T : ℝ) ^ (2 + ε₁ T)) := by sorry

end Supplement

end FasterPrimeEnum
