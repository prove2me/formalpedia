-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_allcap_C1_survivor_terminal_plus_ruin_contact_joint_L1
-- name    : AvramDividend.Classical.avram_bva_a22_original_allcap_C1_survivor_terminal_plus_ruin_contact_joint_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:43:01.660266+00:00
-- url     : https://prove2.me/theorems/64787ecc-abbb-4860-89fb-b5fb0d0d8e9b
-- title:
--   Original all-cap BV C1 true survivor positive terminal omission plus genuine ruin-contact cash is integrable and vanishes in expected value
-- statement:
--   For the actual original standing BV spectrally negative Levy process, admissible dividend control, original full horizon T, arbitrary finite or infinite cap, and C1 verification candidate, show the sum of the actual strict-survivor positive discounted terminal omission beyond the last uniform physical-grid clock and genuine stopped open-interval Stieltjes ruin-contact cash is integrable at every mesh row and has expected value tending to zero. Assume source a.e. strong measurability of the literal survivor terminal omission. This follows from the all-cap zero-boundary terminal L1 theorem and the already Proved BVA97 original clipped ruin-contact L1 theorem. It retains original X, D, paymentTimes, dividendMeasure, physical grid and full-T survivor indicator, with no global generator L1 or finite jump activity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_allcap_C1_strict_survivor_terminal_positive_L1_from_measurability
import Theorems.Thm_AvramDividend_Classical_avram_bva97_original_BV_cash_contact_L1_mean_zero_exact
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

theorem AvramDividend.Classical.avram_bva_a22_original_allcap_C1_survivor_terminal_plus_ruin_contact_joint_L1
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
    let Contact : ℕ → Ω → ℝ := fun m ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal -
          T / ((m : ℝ) + 2))
            ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal
    (∀ m, AEStronglyMeasurable (Err m) P) →
    (∀ m, Integrable (fun ω => Err m ω + Contact m ω) P) ∧
    Tendsto (fun m => ∫ ω, Err m ω + Contact m ω ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
