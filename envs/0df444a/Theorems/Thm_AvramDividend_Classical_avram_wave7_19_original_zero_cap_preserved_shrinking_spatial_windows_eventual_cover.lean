-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_zero_cap_preserved_shrinking_spatial_windows_eventual_cover
-- name    : AvramDividend.Classical.avram_wave7_19_original_zero_cap_preserved_shrinking_spatial_windows_eventual_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:18:42.184746+00:00
-- url     : https://prove2.me/theorems/22ebfe04-1185-4be2-a483-f4c380621d46
-- title:
--   Original pre-ruin zero/cap boundary plus shrinking interior bands eventually cover every payment time
-- statement:
--   For any original capped admissible dividend strategy and any positive lower cutoffs converging to zero and strict upper cutoffs converging to the original cap C in ENNReal, the corresponding spatial bands stay in the precise positive C2 HJB domain and, together with the zero and cap post-rightpayment state boundaries, eventually cover every source time-zero or strictly pre-ruin payment. This is valid at C=top and for arbitrary nonmonotone cutoff sequences. It derives source coverage from existing admissibility and initial-cap hypotheses and retains rightpayment atoms at both boundaries. Does not assert stopping-time grid exits exhaust the clock; time-window coverage and local Ito budgets still require separate proofs.
-- source:
--   Original source capped_postPaymentReserve_initial_state and within_cap_before_ruin; filter-top eventual order-neighbourhood argument for lower/upper spatial thresholds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_within_cap_before_ruin
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_zero_cap_preserved_shrinking_spatial_windows_eventual_cover
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (lower : ℕ → ℝ) (upper : ℕ → ℝ≥0∞)
    (hlower : Filter.Tendsto lower Filter.atTop (𝓝 0))
    (hupper : Filter.Tendsto upper Filter.atTop (𝓝 C))
    (hlower_pos : ∀ n, 0 < lower n)
    (hupper_cap : ∀ n, upper n < C) :
    (∀ n y, lower n < y ∧ ENNReal.ofReal y < upper n →
      0 < y ∧ ENNReal.ofReal y < C) ∧
    (∀ (ω : Ω) (t : ℝ≥0),
      t = 0 ∨ (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
      ∀ᶠ n : ℕ in Filter.atTop,
        x + X.X t ω - rightLimit D t ω = 0 ∨
          ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) = C ∨
            (lower n < x + X.X t ω - rightLimit D t ω ∧
              ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) < upper n)) := by sorry
