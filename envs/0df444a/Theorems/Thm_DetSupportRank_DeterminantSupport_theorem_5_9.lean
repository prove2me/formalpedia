-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_theorem_5_9
-- name    : DetSupportRank.DeterminantSupport.theorem_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:49.353656+00:00
-- url     : https://prove2.me/theorems/7b962eb1-873a-452c-b145-87fd9f567e20
-- title:
--   Theorem 5.9 — Multigraded Hilbert syzygy theorem
-- statement:
--   Let $S=F[x_1,\ldots,x_m]$ have any $\mathbb Z^d$ grading, and let $M$ be a finitely generated graded $S$-module. There exists a resolution
--   $$0\to F_\ell\to\cdots\to F_0\to M\to0,\qquad\ell\le m,$$
--   where every term is finite free, every map preserves degree, and the sequence is exact at every term including both endpoints. No positivity of the ring grading is required.
--
--   This existence result supplies actual finite graded resolutions for the Laurent K-polynomial construction.
--
--   Differences from the source:
--   - encoding: graded modules and degree-preserving maps → actual modules with specified subspaces, an internal direct-sum predicate, and actual linear maps; reason: these are the ordinary graded-module axioms; resolution existence, K identities, and specialization exactness are separate conclusions
--   - encoding: Laurent polynomials in d variables → integer additive monoid algebra on ℤ^d; reason: exponent vectors can be negative; multiplication adds exponents and no infinite series coefficients are used
--   - generalization: S = F[x_1,…,x_m] with positive variable degrees p_j ∈ ℕ^d∖{0} (§5.3, p.18), the remark on p.18 saying positivity is unnecessary → arbitrary integer variable weights p_j ∈ ℤ^d; reason: the source remarks that positivity is not needed for the syzygy theorem and applies it to the nonpositive ℕ^d bigrading in Proposition 5.22; positive and ℕ^d weights are special cases
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Theorem 5.9, p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_FreeResolutions

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Theorem 5.9, p.18. -/
theorem theorem_5_9 {K : Type*} [Field K] {m d : ℕ}
    (p : Fin m → Fin d → ℤ) (M : GradedModuleData K (Fin m) (Fin d))
    (hg : IsGraded p M) (hfg : Module.Finite (MvPolynomial (Fin m) K) M.Carrier) :
    ∃ R : FiniteGradedResolution p M, R.length ≤ m := by sorry

end DetSupportRank.DeterminantSupport
