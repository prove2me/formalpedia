-- Prove2me | Theorems.Thm_EuclideanCRHardness_Covering_lattice_semantics
-- name    : EuclideanCRHardness.Covering.lattice_semantics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:08.982076+00:00
-- url     : https://prove2.me/theorems/52575d24-a4f4-4687-844e-ec8e6e211b56
-- title:
--   Nearest-point attainment and Gram-matrix bridge
-- statement:
--   For an invertible real square matrix $B$, every real target has an integer vector attaining its nearest-lattice distance, the distance range is bounded above, and the covering radius is nonnegative and attained at a real target. Moreover,
--   $$\mu(B\mathbb Z^n)^2=\mu_{B^TB}^2.$$
--   This supporting target connects the actual Euclidean lattice promise to the quadratic quantities without assuming that a finite target grid suffices.
--
--   Differences from the source:
--   - encoding: finite coordinates indexed 1 through n and signs ±1 → Fin n coordinates and Bool signs (true is +1); reason: bijective finite reindexing and sign coding preserve every instance
--   - encoding: minimum and maximum in the source → real infimum and supremum together with separate attainment targets; reason: positive definiteness and invertibility imply nonempty bounded optimization sets and attained extrema; none is assumed as input data
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), equations (1.1) and (2.2), §2 preamble, printed p. 3 / PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf Equation (1.1), printed p. 1 / PDF p. 2.

import Definitions.Def_EuclideanCRHardness_Covering_Quadratic
import Definitions.Def_EuclideanCRHardness_Covering_Lattice

namespace EuclideanCRHardness.Covering

/-- Existence of nearest points, finite covering radius and the exact Gram bridge (2.2). -/
theorem lattice_semantics {n : ℕ} (B : RMat n) (hB : B.det ≠ 0) :
    (∀ y : EuclideanSpace ℝ (Fin n), ∃ z : Fin n → ℤ,
      nearestDistance B y = dist y (latticePoint B z)) ∧
    BddAbove (Set.range (nearestDistance B)) ∧
    (∃ y : EuclideanSpace ℝ (Fin n), coveringRadius B = nearestDistance B y) ∧
    0 ≤ coveringRadius B ∧
    coveringRadius B ^ 2 = muQ2 (B.transpose * B) := by sorry

end EuclideanCRHardness.Covering
