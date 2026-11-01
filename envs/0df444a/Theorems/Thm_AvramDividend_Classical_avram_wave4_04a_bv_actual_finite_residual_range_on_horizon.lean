-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_residual_range_on_horizon
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_finite_residual_range_on_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:37:04.620488+00:00
-- url     : https://prove2.me/theorems/92aa24fb-9706-4627-ad59-287adbd329d0
-- title:
--   Finite-activity bounded-variation original spectrally negative Lévy residual has finite range on every finite horizon
-- statement:
--   For the original finite-negative-intensity bounded-variation source Lévy process on the same Ω and P, for every positive finite horizon T, the actual drift residual path u↦uX.drift−X_u has only finitely many distinct values on [0,T] on a P-full event. No grid hypothesis appears in the final theorem: instantiate the aligned dyadic grid iT/2^n and construct right-covering indices using the already Proved horizon-scaled dyadic ceiling. This is the finite-range precursor to true original compound-Poisson source jump activity.
-- source:
--   Conditional full-horizon original-source finite-range theorem 3045a09b-7a7f-4c33-975b-1fd8e3e9117d is canonically Proved. Proved da8556b4-347e-47d5-9bbf-9b0b87454251 supplies right-scaled dyadic ceiling convergence. Elementary NNReal arithmetic establishes alignment, monotonicity and equal mesh for the concrete grid. This proves the unconditional BV finite-activity source residual finite-range event without a replacement Poisson space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_original_residual_finite_range_of_right_grid

open MeasureTheory Set Filter Topology Finset AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_finite_residual_range_on_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ S : Finset ℝ, ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) * X.drift - X.X t ω ∈ S := by sorry
