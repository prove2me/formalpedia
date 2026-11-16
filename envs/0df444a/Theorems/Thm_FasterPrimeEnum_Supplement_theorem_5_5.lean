-- Prove2me | Theorems.Thm_FasterPrimeEnum_Supplement_theorem_5_5
-- name    : FasterPrimeEnum.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:53:17.622947+00:00
-- url     : https://prove2.me/theorems/8b3f00d2-5cc4-4a15-8975-674b981730a6
-- title:
--   Theorem 5.5 — decompression: recover the unique $a$ with $\kappa(a)=b$, $\mathrm{wt}(a)\le R$, or FAIL
-- statement:
--   In the setting of Theorem 5.2 ($T$, $R\le T/2$, $S=2\lambda R$, $\kappa$ for the fixed $h,\beta$, a fixed multiplication algorithm with (4.2) and transform scheme with $T(n)\ll M(n)$), there is an algorithm with the following properties. Its input is a vector $b\in\mathbb F_2^S$.
--
--   1. If there exists $a\in\mathbb F_2^T$ with $\kappa(a)=b$ and $\mathrm{wt}(a)\le R$, then such $a$ is unique, and the algorithm returns it.
--   2. Otherwise it returns “FAIL”.
--
--   Its running time is
--
--   $$
--   O\big(T\log T\cdot C^*(T)\big)+R(\log T)^{5+o(1)},
--   $$
--
--   after a precomputation depending only on $T$ and $R$ of cost $T(\log T)^{3+o(1)}$.
--
--   Together with Theorem 5.2 this shows that $\kappa$ is injective on vectors of weight at most $R$, and it recovers the odd square-primes of each interval in the core algorithm.
--
--   **Formalization Note** As in Theorem 5.2: two machines, the choice of $(h,\beta)$ per $T$, $\varepsilon_1,\varepsilon_2\to0$ and $K$ before $T,R$. Uniqueness is stated for every pair of vectors of weight at most $R$; the run returns $a$ (answer bit true, $a$ on the output tape) or FAIL (answer bit false).
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) with RunsWithin / RunOutcome (a halted run within the time bound, with exactly the output on a designated tape); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a change of the O-constant or a shift of an o(1) exponent); an existential over the more restricted machine is the stronger statement
--   - reading: the algorithms fixed in §4.1, §4.3 ("we fix …") with the standing assumption (4.2) M(kn) ≪_k M(n) (p.19) → the statement holds for every multiplication algorithm Mul with Mul.Assumption42 and every transform scheme with T(n) ≤ c·M(n); reason: the paper fixes arbitrary such algorithms and assumes (4.2) for the rest of the paper (pp.19, 27, 36); a universal quantifier is exactly "for the fixed ones, whichever they are"
--   - reading: κ for the fixed h and β of §5.1, which the algorithm computes (Lemmas 4.5, 4.7) → a function fd : ℕ → FieldData chosen with the machines, with IsFieldData (lam T) (fd T) for every valid T; reason: the paper's h and β depend only on λ = lg(T + 1) and are computed by the algorithm
--   - encoding: a precomputation (depending only on T and R) followed by the decompression of b → a precomputation machine P on input (T, R) halting with a word pre, and a machine A on input (T, R, pre, b); reason: the two-phase reading of "after a precomputation"; the precomputed data is passed as a word
--   - encoding: output “FAIL” → the machine halts with answer bit false (RunOutcome … none); a returned word is answer bit true with the word on the output tape; reason: the paper fixes no encoding of FAIL; the answer bit makes FAIL distinct from every returned word
--   - encoding: the two o(1) terms → two functions ε₁, ε₂ : ℕ → ℝ of T tending to 0; reason: both o(1) are as T → ∞
--   - encoding: log x and log log x in complexity bounds → logU x = log max(x, 2) and logU (logU x); reason: the paper's convention (p.2): in complexity bounds log x should be read as log max(x, 2)
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 5.5, p.38; §5.1, pp.35–36

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_FasterPrimeEnum_Supplement_RunOutcome
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

/-- **Theorem 5.5 (Decompression)** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851
(held version, sha256 7fc13f17…), p.38.

"There is an algorithm with the following properties. It takes as input a vector b ∈ F₂^S. If
there exists a vector a ∈ F₂^T such that κ(a) = b and wt(a) ⩽ R, then such a is unique, and the
algorithm returns a. Otherwise it returns "FAIL". Its running time is
O(T log T · C*(T)) + R(log T)^{5+o(1)}, after a precomputation (depending only on T and R) of cost
T(log T)^{3+o(1)}."

Setting as in Theorem 5.2 (§5.1–5.2): `T`, `R ⩽ T/2` positive, `S = 2λR`, `κ` for the fixed `h`,
`β`, a fixed transform scheme with `T(n) ≪ M(n)`, and `C*(n) = M*(n) + K*(n)`.

**Formalization Note.** Relative to every multiplication algorithm with (4.2) and every transform
scheme with `T(n) ≤ c M(n)`: a precomputation machine `P`, a main machine `A`, the field data
`(h, β)` for each `T`, `ε₁, ε₂ → 0` (functions of `T`) and `K`, all before `T, R`. For every valid
`T, R`: (1) uniqueness — two vectors of `F₂^T` of weight at most `R` with the same `κ` are equal;
(2) the precomputation halts with a word `pre` within `T (log T)^{3+ε₂(T)}` steps; (3) on every
`b ∈ F₂^S` (a list of `S = 2λR` bits) the main algorithm halts within
`K T log T C*(T) + R (log T)^{5+ε₁(T)}` steps, returning `a` (answer bit `true`, `a` on the output
tape) whenever `a ∈ F₂^T` has `wt(a) ≤ R` and `κ(a) = b`, and returning "FAIL" (answer bit `false`)
when no such `a` exists. Logarithms are clipped (p.2). -/
theorem theorem_5_5 (Mul : MulAlgorithm) (hMul : Mul.Assumption42) (TS : TransformScheme)
    (hT : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → TS.Tcost n ≤ c * Mul.Mcost n) :
    ∃ (P : PrimitiveMachine) (pout : Fin P.tapeCount) (A : PrimitiveMachine) (out : Fin A.tapeCount)
      (fd : ℕ → FieldData) (ε₁ ε₂ : ℕ → ℝ) (K : ℝ),
      Tendsto ε₁ atTop (𝓝 0) ∧ Tendsto ε₂ atTop (𝓝 0) ∧ 0 < K ∧
      ∀ T R : ℕ, 0 < T → 0 < R → 2 * R ≤ T →
        IsFieldData (lam T) (fd T) ∧
        (∀ a a' : List Bool, a.length = T → a'.length = T → a.count true ≤ R →
          a'.count true ≤ R → kappa (fd T) T R a = kappa (fd T) T R a' → a = a') ∧
        ∃ pre : List Bool,
          RunsWithin P pout (Encoding.encodeList id [binWord T, binWord R]) pre
            ((T : ℝ) * logU (T : ℝ) ^ (3 + ε₂ T)) ∧
          ∀ b : List Bool, b.length = 2 * lam T * R →
            (∀ a : List Bool, a.length = T → a.count true ≤ R → kappa (fd T) T R a = b →
              RunOutcome A (A.init (Encoding.encodeList id [binWord T, binWord R, pre, b])) out
                (K * (T : ℝ) * logU (T : ℝ) * Cstar Mul TS T +
                  (R : ℝ) * logU (T : ℝ) ^ (5 + ε₁ T)) (some a)) ∧
            ((¬ ∃ a : List Bool, a.length = T ∧ a.count true ≤ R ∧ kappa (fd T) T R a = b) →
              RunOutcome A (A.init (Encoding.encodeList id [binWord T, binWord R, pre, b])) out
                (K * (T : ℝ) * logU (T : ℝ) * Cstar Mul TS T +
                  (R : ℝ) * logU (T : ℝ) ^ (5 + ε₁ T)) none) := by sorry

end Supplement

end FasterPrimeEnum
