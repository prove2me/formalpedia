-- Prove2me | Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_admissible_infinite_cap
-- name    : AvramDividend.Classical.drained_zero_barrier_admissible_infinite_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:35:19.186142+00:00
-- url     : https://prove2.me/theorems/98aedb39-b4a1-472b-ae28-529c4b79b233
-- title:
--   Instantly ruined drained zero-barrier policy is admissible under the infinite cap
-- statement:
--   For every spectrally negative Lévy process and nonnegative initial capital, the zero-barrier strategy plus a continuous unit-rate dividend drain is an admissible dividend strategy with infinite reserve cap. Ruin is instantaneous, so the strict pre-ruin payment constraints are vacuous, and the initial lump sum equals the initial reserve. The infinite cap makes the cap constraint automatic. This is a pathwise ingredient for identifying the omitted nonnegative boundary-value assumption in Proposition 4(i).
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 2 admissibility definition, plus the previously proved zero-barrier strategy, continuous drain and immediate ruin lemmas.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain_initial_rightLimit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_ruinTime_zero

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.drained_zero_barrier_admissible_infinite_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x) :
    IsAdmissibleLe X x ⊤
      (fun t ω => barrierStrategy X x 0 t ω + (t : ℝ)) := by sorry
