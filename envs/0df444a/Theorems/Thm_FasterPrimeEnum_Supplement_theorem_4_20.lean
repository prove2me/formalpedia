-- Prove2me | Theorems.Thm_FasterPrimeEnum_Supplement_theorem_4_20
-- name    : FasterPrimeEnum.Supplement.theorem_4_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:51:20.101205+00:00
-- url     : https://prove2.me/theorems/7f1d36d1-4f31-4380-8b62-e68c123f99cf
-- title:
--   Theorem 4.20 — a transform scheme with $K(n)\ll n\cdot4^{\log^*n}$ and $T(n)\ll M(n)$
-- statement:
--   Fix a multiplication algorithm for $\mathbb F_2[x]$ with cost function $M(n)$ (§4.1), subject to the paper's standing assumption $M(kn)\ll_k M(n)$ (4.2). Then there exists a transform scheme over $\mathbb F_2$ (Definitions 4.17–4.18) achieving
--
--   $$
--   K(n)\ll n\cdot4^{\log^*n}\qquad\text{and}\qquad T(n)\ll M(n),
--   $$
--
--   where $K(n)=n\max_{m\le n}K_m/m$ is the smoothed transform length, $T(n)$ the running time of the forward and inverse transforms, and $\log^*$ the iterated natural logarithm.
--
--   The multiplication algorithm is used as a black box. The resulting scheme is the one the core algorithm (§6) and compression (§5) use for products with a recurring operand.
--
--   **Formalization Note** Each $\ll$ is a constant $c>0$ with the bound for every $n\ge1$.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) with RunsWithin / RunOutcome (a halted run within the time bound, with exactly the output on a designated tape); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a change of the O-constant or a shift of an o(1) exponent); an existential over the more restricted machine is the stronger statement
--   - encoding: polynomials in F₂[x]_n and vectors in F₂^K → functions Fin n → ZMod 2 and Fin K → ZMod 2, given to machines as bit arrays in index order (vecBits); an input of degree < n is an array of exactly n bits; reason: the paper represents polynomials by their coefficient arrays in the monomial basis (p.19); the worst case over inputs of degree < n is the worst case over n-bit arrays
--   - reading: Given a multiplication algorithm for F₂[x] with associated cost function M(n) → for every MulAlgorithm satisfying Assumption42 ((4.2): M(kn) ≤ c_k M(n) for all n ≥ 1); reason: (4.2) is a standing assumption of the paper from p.19 on ("For technical reasons it will also be convenient to assume (4.2) for each k ⩾ 1")
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 4.20, p.24; §4.1, p.19; Definitions 4.17–4.18, pp.23–24

import Mathlib
import Definitions.Def_FasterPrimeEnum_Supplement_MulAlgorithm
import Definitions.Def_FasterPrimeEnum_Supplement_TransformScheme
import Definitions.Def_FasterPrimeEnum_Supplement_logStar

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

/-- **Theorem 4.20** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version,
sha256 7fc13f17…), p.24.

"Given a multiplication algorithm for F₂[x] with associated cost function M(n), there exists a
transform scheme achieving (4.4) K(n) ≪ n · 4^{log* n} (or equivalently, K*(n) ≪ 4^{log* n}) and
(4.5) T(n) ≪ M(n)."

**Formalization Note.** For every multiplication algorithm `Mul` (a machine multiplying all
polynomials of `F₂[x]_n`, every `n ≥ 1`) satisfying the paper's standing assumption (4.2) (p.19:
"For technical reasons it will also be convenient to assume that M(kn) ≪_k M(n) for each k ⩾ 1"),
there is a transform scheme (Definitions 4.17–4.18) with `K(n) ≤ c n 4^{log* n}` and
`T(n) ≤ c' M(n)` for all `n ≥ 1`, with constants chosen before `n`. `M`, `K`, `T` are the cost
functions of p.19 and pp.23–24; `log*` iterates the natural logarithm (p.1). -/
theorem theorem_4_20 (Mul : MulAlgorithm) (hMul : Mul.Assumption42) :
    ∃ TS : TransformScheme,
      (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → TS.Kcost n ≤ c * (n : ℝ) * 4 ^ logStar (n : ℝ)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → TS.Tcost n ≤ c * Mul.Mcost n) := by sorry

end Supplement

end FasterPrimeEnum
