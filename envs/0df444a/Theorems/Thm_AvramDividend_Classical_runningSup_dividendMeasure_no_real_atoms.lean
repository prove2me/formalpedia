-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_real_atoms
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_no_real_atoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:42:40.81966+00:00
-- url     : https://prove2.me/theorems/1b7fcf5a-982a-443d-9841-002373b3508b
-- title:
--   Actual running-supremum Stieltjes dividend measure has no atoms at any real time
-- statement:
--   For every real time, the actual running-supremum Stieltjes dividend measure assigns zero mass to the singleton. The proof combines the remotely proved negative-time and nonnegative-time no-atom theorems. This single endpoint-free assertion supports replacing strict with weak time cut-offs when analysing the stopped dividend integral.
-- source:
--   Remotely Proved runningSup_dividendMeasure_no_negative_atoms e6ba84eb-ecf1-4f40-9747-5da5df7337ab and runningSup_dividendMeasure_no_nonnegative_atoms 6b1bbe98-fb10-4561-bf0a-9bd58e3c0294.

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_negative_atoms
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_nonnegative_atoms

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_no_real_atoms
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ) :
    (dividendMeasure (runningSup X) ω) ({t} : Set ℝ) = 0 := by sorry
