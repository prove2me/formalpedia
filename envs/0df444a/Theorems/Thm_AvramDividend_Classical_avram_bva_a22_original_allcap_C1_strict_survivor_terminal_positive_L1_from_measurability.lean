-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_allcap_C1_strict_survivor_terminal_positive_L1_from_measurability
-- name    : AvramDividend.Classical.avram_bva_a22_original_allcap_C1_strict_survivor_terminal_positive_L1_from_measurability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:26:17.306905+00:00
-- url     : https://prove2.me/theorems/b1dc4102-891f-4aa8-bb49-e8a9ad4f07b4
-- title:
--   Original all-cap BV C1 strictly surviving full-horizon terminal positive omitted error vanishes in mean from measurability
-- statement:
--   For the actual original standing BV spectrally negative Levy source and any positive or infinite dividend cap C, the admissible original dividend strategy and continuous nonnegative-at-zero C1 HJB candidate with interior slope at least one, prove that the true full-horizon discounted survivor candidate positive omission beyond the last prescribed strict uniform physical-grid clock has mean tending to zero from row a.e. strong measurability. The proof reduces to the finite-cap and infinite-cap source exact theorems by the exhaustive dichotomy C=top or C!=top, retaining the original X, D, T, strict ruin, and post-right-payment reserves. This removes the cap branch from the BVA96 survivor terminal error and requires no finite negative-jump activity or global generator L1.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_finitecap_C1_strict_survivor_terminal_positive_L1_from_measurability
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_topcap_C1_strict_survivor_terminal_positive_L1_from_measurability
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_finitecap_strict_survival_both_endpoints_closed_clipped_band
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_candidate_zero_boundary_uniform_modulus
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_survivor_terminal_positive_omission_integrable_from_measurability
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_survivor_closedband_discounted_terminal_positive_L1
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_allcap_C1_strict_survivor_terminal_positive_L1_from_measurability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ))) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (x + X.X t ω - rightLimit D t ω))
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    (∀ m, AEStronglyMeasurable (Err m) P) →
    Tendsto (fun m => ∫ ω, Err m ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
