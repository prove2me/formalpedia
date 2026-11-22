-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_bernstein_infinite_activity_potential_atom_zero
-- name    : AvramDividend.Classical.killed_bernstein_infinite_activity_potential_atom_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T15:40:45.906541+00:00
-- url     : https://prove2.me/theorems/55603110-1863-43cd-94ac-4a1b5bce74b6
-- title:
--   Infinite activity forces absence of zero atom in finite killed Bernstein potential
-- statement:
--   For the reciprocal-Laplace killed Bernstein renewal potential U with finite mass 1/k and nonnegative support, prove its atom at zero vanishes if the original Lévy measure κ has infinite mass on (0,1]. By monotone convergence the Bernstein exponent diverges at increasing integer frequencies, so its inverse Laplace transform tends to zero. Then use the previously Proved natural-exponential-Laplace atom extractor. This isolates the zero-atom part of the full regularity theorem 8c56d3e5.
-- source:
--   Proved b6e59826, generic Laplace-inverse atom0 9f464a39; K infinite source original 8f9e6281 and Esscher weight 011d0df2.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.killed_bernstein_infinite_activity_potential_atom_zero (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iic (0 : ℝ)) = 0)
    (k : ℝ) (hk : 0 < k)
    (hFin : ∀ s : ℝ, 0 < s →
      (∫⁻ t : ℝ, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ) ≠ ⊤)
    (U : Measure ℝ)
    (hUsupp : U (Iio (0 : ℝ)) = 0)
    (hUmass : U Set.univ = ENNReal.ofReal (k⁻¹))
    (hULap : ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(s * y))) ∂U) =
        (ENNReal.ofReal k +
          (∫⁻ t : ℝ,
            ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ))⁻¹)
    (hκinf : κ (Ioc (0 : ℝ) 1) = ⊤) :
    U {(0 : ℝ)} = 0 := by sorry
