-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_k_hilbert_agreement
-- name    : DetSupportRank.DeterminantSupport.k_hilbert_agreement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:27.434636+00:00
-- url     : https://prove2.me/theorems/5dd71dcf-f01c-4576-aca6-7ca24ad7c035
-- title:
--   The positive Hilbert numerator agrees with the resolution-defined K-polynomial
-- statement:
--   Let $S=F[x_1,\ldots,x_m]$ have nonzero nonnegative variable multidegrees $p_j$. Let $M$ be a finitely generated nonnegatively graded $S$-module. Then all homogeneous pieces are finite dimensional and
--   $$K_M^S(t)=H_M(t)\prod_j(1-t^{p_j})$$
--   is a polynomial. Embedded into the Laurent ring, it equals the resolution-defined K-polynomial. Nonnegative grading means that every piece with a negative coordinate is zero.
--
--   This target justifies use of the positive definition and rules out any default value from an infinite-dimensional component or an unproved polynomiality assertion.
--
--   Differences from the source:
--   - encoding: graded modules and degree-preserving maps → actual modules with specified subspaces, an internal direct-sum predicate, and actual linear maps; reason: these are the ordinary graded-module axioms; resolution existence, K identities, and specialization exactness are separate conclusions
--   - encoding: Laurent polynomials in d variables → integer additive monoid algebra on ℤ^d; reason: exponent vectors can be negative; multiplication adds exponents and no infinite series coefficients are used
--   - encoding: a module graded by ℕ^d → an integer grading with all pieces having a negative coordinate equal to zero; reason: extension by zero is exactly the same nonnegative grading
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Remark 5.10 and Definitions 5.4–5.6, p. 19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_HilbertSeries
import Definitions.Def_DetSupportRank_DeterminantSupport_Cokernels

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Remark 5.10 and §5.3, p.19. -/
theorem k_hilbert_agreement {K : Type*} [Field K] {m d : ℕ}
    (p : Fin m → Fin d → ℕ) (hp : ∀ j, p j ≠ 0)
    (M : GradedModuleData K (Fin m) (Fin d))
    (hg : IsGraded (fun j i => (p j i : ℤ)) M)
    (hfg : Module.Finite (MvPolynomial (Fin m) K) M.Carrier)
    (hnonneg : ∀ u : Fin d → ℤ, (∃ i, u i < 0) → M.piece u = ⊥) :
    (∀ u, FiniteDimensional K (M.piece u)) ∧
    ((positiveKPolynomial p M : MvPowerSeries (Fin d) ℤ) = hilbertNumerator p M) ∧
    kPolynomial (fun j i => (p j i : ℤ)) M = naturalToLaurent (positiveKPolynomial p M) := by sorry

end DetSupportRank.DeterminantSupport
