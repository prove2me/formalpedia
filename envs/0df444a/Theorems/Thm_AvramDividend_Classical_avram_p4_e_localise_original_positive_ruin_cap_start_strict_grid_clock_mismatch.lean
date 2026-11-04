-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_ruin_cap_start_strict_grid_clock_mismatch
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_positive_ruin_cap_start_strict_grid_clock_mismatch
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:27:29.685333+00:00
-- url     : https://prove2.me/theorems/e7736263-eb08-4c63-af88-85ec1be26e97
-- title:
--   Original positive-ruin clock is strictly later than unpaid-cap strict interior grid exit
-- statement:
--   For an actual original SpectrallyNegativeLevy X and genuine admissible finite cap c, if x=c>0, time-zero right dividend is absent and the observation grid begins at zero, the first exit from any strict upper subcap band occurs at zero. If the actual original controlled ruin time is additionally strictly positive, then for each positive fixed horizon the canonical stopped clock (min ruinTime n).toNNReal is strictly positive. This supplies a source-exact conditional mismatch of the two localisation schemes. The positive-ruin premise is explicit and cannot be silently inferred from interior HJB hypotheses.
-- source:
--   Composes Proved original P4-E cap-start strict-grid exit clock 5c4bb464-106d-463b-91aa-f0cac6981367 with Proved exact positive horizon zero clock iff immediate ruin c28dcd9b-e834-435d-88c2-9071d42da516.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_cap_start_inner_band_grid_exit_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_horizon_zero_clock_iff_immediate_ruin
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At positive ruin an unpaid cap-start separates strict grid exit from the real ruin clock. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_positive_ruin_cap_start_strict_grid_clock_mismatch
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (c x : ℝ) (hc : 0 < c) (hxc : x = c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (hNoInitialPayment : rightLimit D 0 ω = 0)
    (r : ℕ → ℝ≥0) (hr0 : r 0 = 0)
    (lower upper : ℝ) (hUpper : upper < c)
    (n : ℕ) (hn : 0 < n)
    (hRuinPos : 0 < ruinTime X x D ω) :
    min (⨅ k : ℕ,
      if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
         upper < x + X.X (r k) ω - rightLimit D (r k) ω
      then (r k : WithTop ℝ≥0) else ⊤) (n : WithTop ℝ≥0) =
        (0 : WithTop ℝ≥0) ∧
    0 < (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by sorry
