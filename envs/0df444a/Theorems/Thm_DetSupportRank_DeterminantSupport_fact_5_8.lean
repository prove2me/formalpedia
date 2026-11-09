-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_fact_5_8
-- name    : DetSupportRank.DeterminantSupport.fact_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:25.135618+00:00
-- url     : https://prove2.me/theorems/7392a7c6-6608-4c50-8597-cf32a60fc1e1
-- title:
--   Fact 5.8 — K-polynomial of a shifted free module
-- statement:
--   For a polynomial ring $S$ over any field, with any integer multigrading, let $S^s$ have $k$ basis vectors of degrees $s_1,\ldots,s_k\in\mathbb Z^d$. Then
--   $$K_{S^s}^S(t)=\sum_{i=1}^k t^{s_i}.$$
--   The empty free module gives zero. This formula remains valid for the negative shifts used after regrading.
--
--   Differences from the source:
--   - encoding: graded modules and degree-preserving maps → actual modules with specified subspaces, an internal direct-sum predicate, and actual linear maps; reason: these are the ordinary graded-module axioms; resolution existence, K identities, and specialization exactness are separate conclusions
--   - encoding: Laurent polynomials in d variables → integer additive monoid algebra on ℤ^d; reason: exponent vectors can be negative; multiplication adds exponents and no infinite series coefficients are used
--   - generalization: nonnegative basis shifts and positive variable weights in Fact 5.8 → integer basis shifts and arbitrary integer variable weights; reason: the resolution-defined extension of §5.3 has exactly this formula; restricting to the source weights and shifts recovers Fact 5.8
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Fact 5.8, p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_KPolynomials

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Fact 5.8, p.18. -/
theorem fact_5_8 {K : Type*} [Field K] {m d k : ℕ}
    (p : Fin m → Fin d → ℤ) (s : Fin k → Fin d → ℤ) :
    kPolynomial p (freeModuleData (K := K) p s) =
      ∑ i, AddMonoidAlgebra.single (s i) (1 : ℤ) := by sorry

end DetSupportRank.DeterminantSupport
