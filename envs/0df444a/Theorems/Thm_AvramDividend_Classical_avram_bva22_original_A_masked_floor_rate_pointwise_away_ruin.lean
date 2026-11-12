-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva22_original_A_masked_floor_rate_pointwise_away_ruin
-- name    : AvramDividend.Classical.avram_bva22_original_A_masked_floor_rate_pointwise_away_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:41:29.826201+00:00
-- url     : https://prove2.me/theorems/ca3d19af-b3c4-4c2e-9b34-203b32e7ad55
-- title:
--   Original A stopped inclusive-cap floor kernel converges pointwise at all positive non-ruin times
-- statement:
--   For the original no-jump Standing-BV source, the exact masked floor-grid A negative-mark kernel converges for every positive t≤S outside the unique ruin time to the true discounted pre-ruin cap-masked mark kernel. If t<ruin, the Proved original pre-ruin floor kernel convergence 11fd0ffd and original closed-cap reserve a009975c apply. If ruin<t, the Proved original natural floor postruin mask eventual-vanishing 0b378861 makes all sufficiently fine samples zero. The cases are exhaustive away from ruin and give exactly the almost-everywhere A-side limit required for the original 7ccc2a1a paired DCT, preserving X, P, D, ν, discount and cap.
-- source:
--   Original actual A-grid compensated mark integrand pointwise convergence away from unique ruin instant for 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_original_preruin_masked_uniform_floor_kernel_converges
import Theorems.Thm_AvramDividend_Classical_avram_bva20_postruin_uniform_nat_floor_mask_eventually_false
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva22_original_A_masked_floor_rate_pointwise_away_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hNotRuin : (t : ℝ≥0∞) ≠ ruinTime X x D ω)
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
    let F : ℝ≥0 → ℝ := fun r => Real.exp (-(q * (r : ℝ))) *
      ∫ z in Iio (0 : ℝ), w (U r + z) - w (U r) ∂X.ν
    Tendsto (fun n =>
      if (s n : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C then F (s n) else 0)
      atTop (𝓝 (if (t : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then F t else 0)) := by sorry
