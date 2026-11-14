-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_strict_survival_both_terminal_endpoints_closed_band
-- name    : AvramDividend.Classical.avram_bva_a22_original_BV_strict_survival_both_terminal_endpoints_closed_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:38:49.935198+00:00
-- url     : https://prove2.me/theorems/1742fd0f-0a77-4005-a474-eb29b9ce5b32
-- title:
--   Original BV strict-survival last-grid and full-horizon reserves both occupy a fixed closed zero-inclusive physical band
-- statement:
--   On the original standing bounded-variation Levy process and admissible dividend strategy, strict full-horizon survival implies that both the last grid reserve at T-T/(m+2) and the true horizon reserve lie in the deterministic closed interval [0,x+T drift] simultaneously for every actual uniform physical-grid row, almost surely. This preserves original source clocks, cap and ruin conventions without an extra drift sign condition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_full_preruin_postpayment_closed_physical_drift_strip
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_BV_strict_survival_both_terminal_endpoints_closed_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∀ᵐ ω ∂P, ∀ m : ℕ,
      (S : ℝ≥0∞) < ruinTime X x D ω →
      (x + X.X (u m (m + 1)) ω -
        rightLimit D (u m (m + 1)) ω) ∈
          Icc (0 : ℝ) (x + T * X.drift) ∧
      (x + X.X S ω - rightLimit D S ω) ∈
          Icc (0 : ℝ) (x + T * X.drift) := by sorry
