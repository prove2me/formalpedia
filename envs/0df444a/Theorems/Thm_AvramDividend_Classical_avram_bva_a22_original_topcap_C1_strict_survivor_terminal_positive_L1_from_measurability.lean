-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_topcap_C1_strict_survivor_terminal_positive_L1_from_measurability
-- name    : AvramDividend.Classical.avram_bva_a22_original_topcap_C1_strict_survivor_terminal_positive_L1_from_measurability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:15:32.441205+00:00
-- url     : https://prove2.me/theorems/c1bdd1d5-6cd6-4e7c-af55-f1b8e10e30cc
-- title:
--   Original top-cap BV C1 strictly surviving true-horizon terminal omission vanishes in expected value
-- statement:
--   For the actual original standing bounded-variation Levy X and admissible dividend D with infinite cap, true-horizon strict survival and a positive q, the discounted terminal candidate positive omission beyond the last prescribed uniform physical grid clock has expected value tending to zero given almost-everywhere measurability of its literal source. The HJB candidate is continuous on nonnegative reserves, C1 inside and has derivative at least one, with nonnegative boundary value. Existing source-specific full-horizon closed reserve band, candidate monotonicity, Heine-Cantor and terminal envelope integrability imply the expected omission limit without global generator L1, finite activity or a replacement process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_strict_survival_both_terminal_endpoints_closed_band
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_candidate_zero_boundary_uniform_modulus
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_survivor_terminal_positive_omission_integrable_from_measurability
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_survivor_closedband_discounted_terminal_positive_L1
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_topcap_C1_strict_survivor_terminal_positive_L1_from_measurability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (C : ℝ≥0∞) (hC : 0 < C)
    (hCtop : C = ⊤) (w : ℝ → ℝ)
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
