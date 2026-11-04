-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_cap_start_strict_grid_clocks_sup_zero_vs_true
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_cap_start_strict_grid_clocks_sup_zero_vs_true
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:35:46.721475+00:00
-- url     : https://prove2.me/theorems/f8623cfb-307d-4e23-8173-c912e86b1fc8
-- title:
--   Countably many strict interior grid exits cannot exhaust positive original capped-ruin time from an unpaid cap start
-- statement:
--   For any countable sequence of grid observation schedules starting at time zero and arbitrary strict upper bands below the admissible cap, the supremum of all original-process strict interior first-exit clocks is exactly zero at an unpaid cap start. Independently, if the actual source ruin time is positive and the fixed horizon is positive, its canonical clipped clock is strictly positive. Thus no such sequence can exhaust the exact original ruin clock on those paths. No assumed boundary occupation cancellation, no stochastic convergence and no existential control claim.
-- source:
--   Proved source original strict-band grid exit 5c4bb464-106d-463b-91aa-f0cac6981367 and exact original zero-ruin-clock characterisation c28dcd9b-e834-435d-88c2-9071d42da516.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_cap_start_inner_band_grid_exit_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_horizon_zero_clock_iff_immediate_ruin
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every strict subcap grid clock is zero at an unpaid cap start, although true ruin can be later. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_cap_start_strict_grid_clocks_sup_zero_vs_true
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (c x : ℝ) (hc : 0 < c) (hxc : x = c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (hNoInitialPayment : rightLimit D 0 ω = 0)
    (r : ℕ → ℕ → ℝ≥0) (hr0 : ∀ k, r k 0 = 0)
    (lower upper : ℕ → ℝ) (hUpper : ∀ k, upper k < c)
    (n : ℕ) (hn : 0 < n)
    (hRuinPos : 0 < ruinTime X x D ω) :
    (⨆ k : ℕ, min (⨅ j : ℕ,
      if x + X.X (r k j) ω - rightLimit D (r k j) ω < lower k ∨
         upper k < x + X.X (r k j) ω - rightLimit D (r k j) ω
      then (r k j : WithTop ℝ≥0) else ⊤) (n : WithTop ℝ≥0)) =
        (0 : WithTop ℝ≥0) ∧
    0 < (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by sorry
