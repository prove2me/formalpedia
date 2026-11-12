-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_physical_discounted_mark_uniform_floor_converges
-- name    : AvramDividend.Classical.avram_bvb_b21_original_physical_discounted_mark_uniform_floor_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:33:31.906115+00:00
-- url     : https://prove2.me/theorems/3ef2e568-893d-49c7-8aac-696bed60ebc2
-- title:
--   Original stopped marked compensator kernel converges at genuine positive pre-ruin floor-grid times
-- statement:
--   At every positive strictly pre-ruin original time, under source-zero jumps and Standing BV, the actual discounted mark-integrated prepayment reserve kernel converges from canonical refining uniform floor-grid samples. The inclusive reserve cap is certified at each sample by the already Proved original left-limit closed-cap theorem, and diffuse negative marks and measurability follow the original Standing BV and zero-negative value hypotheses. There is no additional pointwise cap premise or artificial state replacement.
-- source:
--   Pointwise pre-ruin source-exact sampled mark-kernel limit required for 7ccc2a1a original inclusive K-minus-A quadrature.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b21_original_physical_discounted_mark_uniform_floor_converges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hpre : (t : ℝ≥0∞) < ruinTime X x D ω)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q T : ℝ) (hT : 0 < T) :
    let s : ℕ → ℝ≥0 := fun n => Real.toNNReal
      (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    Tendsto (fun n => Real.exp (-(q * (s n : ℝ))) *
      ∫ z in Iio (0 : ℝ), w (U (s n) + z) - w (U (s n)) ∂X.ν)
      atTop (𝓝 (Real.exp (-(q * (t : ℝ))) *
        ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν)) := by sorry
