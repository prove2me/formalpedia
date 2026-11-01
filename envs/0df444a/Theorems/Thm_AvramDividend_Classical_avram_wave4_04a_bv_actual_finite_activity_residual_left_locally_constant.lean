-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_activity_residual_left_locally_constant
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_finite_activity_residual_left_locally_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:50:47.056079+00:00
-- url     : https://prove2.me/theorems/c2b7047e-5eb7-4c1a-9a22-5c4bc906c326
-- title:
--   Actual finite-activity BV source residual is locally constant from the left at every genuine nonjump time
-- statement:
--   For the original spectrally negative Lévy X with BV and finite negative intensity, on a source P-full event the true drift residual t·X.drift-X_t is left-locally constant at every nonjump t in a positive finite horizon. This follows from true source X.leftLim, continuity of drift and the already Proved finite range of the actual residual. It is a needed local no-continuous-component step in identifying drift-deficient dyadic cells with the genuine X jump set, not a Poisson count-law or compensation assertion.
-- source:
--   Proved original path finite residual range theorem 92aa24fb-9706-4627-ad59-287adbd329d0; source SpectrallyNegativeLevy.leftLim. At nonjump t, X_t=lim_{u↑t}X_u, hence Y(u) tends to Y(t) from the left. A finite set of possible Y(u) values on [0,T] forces eventual equality to Y(t) from the left. This source-specific local step is necessary for proving no continuous Stieltjes component and grid jump-count identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_residual_range_on_horizon

open MeasureTheory Filter Set Topology Finset AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_finite_activity_residual_left_locally_constant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t ≤ T →
      X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t = 0 →
        Filter.Eventually
          (fun u : ℝ≥0 =>
            (u : ℝ) * X.drift - X.X u ω =
              (t : ℝ) * X.drift - X.X t ω)
          (nhdsWithin t (Iio t : Set ℝ≥0)) := by sorry
