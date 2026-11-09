-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_k_resolution_independent
-- name    : DetSupportRank.DeterminantSupport.k_resolution_independent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:48.532203+00:00
-- url     : https://prove2.me/theorems/273b7a7b-97b8-40d7-99f1-b396fce1c936
-- title:
--   Resolution-defined K-polynomials are independent of the resolution
-- statement:
--   Let $S=F[x_1,\ldots,x_m]$ be integer multigraded, let $M$ be graded, and let $F_\bullet\to M$ be any actual finite graded free resolution, with shifts $s_{i,j}$. Then
--   $$K_M^S=\sum_{i=0}^{\ell}(-1)^i\sum_jt^{s_{i,j}}.$$
--   The left side is the computed K-polynomial selected from the set of resolutions. Thus every resolution gives the same Laurent polynomial; independence is not an axiom in the definition.
--
--   Differences from the source:
--   - encoding: graded modules and degree-preserving maps → actual modules with specified subspaces, an internal direct-sum predicate, and actual linear maps; reason: these are the ordinary graded-module axioms; resolution existence, K identities, and specialization exactness are separate conclusions
--   - encoding: Laurent polynomials in d variables → integer additive monoid algebra on ℤ^d; reason: exponent vectors can be negative; multiplication adds exponents and no infinite series coefficients are used
--   - generalization: resolution independence for Z^d-graded modules over S with the §5.3 variable degrees (p.19) → arbitrary integer variable weights p_j ∈ ℤ^d and every module admitting a finite graded free resolution; reason: the source states the formula makes sense without positivity; the Tor/Euler-characteristic argument uses no sign condition; the source weights are special cases
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §5.3, independence of the chosen resolution, p. 19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_KPolynomials

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, §5.3, resolution independence, p.19. -/
theorem k_resolution_independent {K : Type*} [Field K] {m d : ℕ}
    (p : Fin m → Fin d → ℤ) (M : GradedModuleData K (Fin m) (Fin d))
    (hg : IsGraded p M) (R : FiniteGradedResolution p M) :
    kPolynomial p M = resolutionEuler R := by sorry

end DetSupportRank.DeterminantSupport
