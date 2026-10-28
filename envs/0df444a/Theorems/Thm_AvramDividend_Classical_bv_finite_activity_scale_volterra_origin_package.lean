-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_volterra_origin_package
-- name    : AvramDividend.Classical.bv_finite_activity_scale_volterra_origin_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:30:31.594148+00:00
-- url     : https://prove2.me/theorems/e5a4ab8a-3a8d-4948-ba1f-7bed7bea756f
-- title:
--   Finite-activity scale renewal equation with vanishing local convolution at zero
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process with finite negative-jump intensity, the canonical q-scale function W has W(0)=1/d and satisfies the local finite-activity Volterra derivative identity W'(x)=((q+lambda)/d)W(x)-G(x)/d on x>0, where the convolution remainder G tends to zero from the right. This is the exact remaining analytic ingredient for finite-activity zero-barrier scale boundary data, independent of payout laws.
-- source:
--   Avram, Palmowski and Pistorius (2007) q-scale Laplace representation; local renewal argument in artifacts/mission_research/1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43/finite-activity-local-renewal-c1-2026-10-25.md. Convolution may be taken as the negative jump-magnitude finite measure applied to W(x-z).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.Algebra.Order.Field
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_scale_volterra_origin_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    W 0 = 1 / X.drift ∧
      ∃ G : ℝ → ℝ,
        ContinuousWithinAt W (Ioi (0 : ℝ)) 0 ∧
        Tendsto G (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) ∧
        (∀ x : ℝ, 0 < x →
          deriv W x =
            ((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift) * W x -
              G x / X.drift) := by sorry
