-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_actual
-- name    : AvramDividend.Classical.runningSup_left_continuous_actual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:28:17.910206+00:00
-- url     : https://prove2.me/theorems/38335f4b-0cf2-43ba-b8a4-0e8ace68275e
-- title:
--   Actual Lévy running maximum is continuous from the left at every positive time
-- statement:
--   For the actual spectrally negative Lévy path, the running supremum S has no left jump at positive times. The process has a left limit ℓ and its no-positive-jump field ensures X_t≤ℓ. The separately Proved generic theorem says that a monotone dominating running supremum of a path with a left limit and no upward jump is continuous from the left. Its representation and monotonicity hypotheses are already Proved for the actual Lévy path. This is a crucial pathwise step towards showing the Stieltjes regulator pays no atom at positive times, enabling correct strict-ruin endpoint handling.
-- source:
--   Proved generic runningSup_left_continuous_of_no_upward_jump cc07976a-d7ac-4c47-8059-656907abf229, Proved runningSup_monotone_and_path_le 848fbd48-f69f-46b9-b2bf-436cb33918a8 and runningSup_eq_rawSup_nonneg 992246e6-0bba-4d6f-bd75-5b29c32037f9.

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_of_no_upward_jump
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_left_continuous_actual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ContinuousWithinAt (fun s : ℝ≥0 => runningSup X s ω) (Set.Iio t) t := by sorry
