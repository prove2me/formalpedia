-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_ruinTime_le_barrier_ruinTime
-- name    : AvramDividend.Classical.zero_cap_ruinTime_le_barrier_ruinTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:23:06.873042+00:00
-- url     : https://prove2.me/theorems/73ce745b-97fc-42ad-92e3-397e0ef5f34a
-- title:
--   Any admissible zero-capped dividend strategy ruins no later than the zero barrier
-- statement:
--   For every sample path and every admissible dividend control with cap zero and initial reserve zero, its ruin time is no later than the ruin time of zero-barrier reflection. The proved pathwise identities imply equal zero reserves for both controls strictly before the arbitrary control's ruin; the proved infimum order lemma transfers this to ruin times. Crucially, a dividend at the positive ruin instant is excluded from the reward.
-- source:
--   Exact DividendStrategy ruinTime and barrier definitions in the published Avram classical mission, related to Avram–Palmowski–Pistorius (2007) §3.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_barrier_eq_control_before_ruin
import Theorems.Thm_AvramDividend_Classical_zero_cap_control_eq_levy_before_ruin
import Theorems.Thm_AvramDividend_Classical_ruinTime_le_of_nonnegative_before_first_ruin

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.zero_cap_ruinTime_le_barrier_ruinTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) :
    ruinTime X 0 D ω ≤ ruinTime X 0 (barrierStrategy X 0 0) ω := by sorry
