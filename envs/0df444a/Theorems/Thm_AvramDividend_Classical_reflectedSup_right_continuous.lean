-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_right_continuous
-- name    : AvramDividend.Classical.reflectedSup_right_continuous
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T11:22:44.324975+00:00
-- url     : https://prove2.me/theorems/aed33f06-6482-4d51-898d-5f3c5630f827
-- title:
--   The actual spectrally negative Lévy drawdown is right-continuous
-- statement:
--   Every càdlàg spectrally negative Lévy path X has a right-continuous running supremum S and a right-continuous reflected drawdown S−X. The theorem instantiates the already proved generic continuity of a monotone dominating running supremum using the newly authored actual monotonicity and domination result, the proved exact raw supremum representation, and the right-continuity field of SpectrallyNegativeLevy. Subtraction of two right-continuous real paths preserves continuity within the forward time interval. This removes the explicit right-continuity hypothesis from the killed-regulator strict first-passage bridge.
-- source:
--   Prove2Me proved generic runningSup_right_continuous_of_right_continuous f0c2320c-8218-484b-9054-75090ac9c401, raw supremum representation 992246e6-0bba-4d6f-bd75-5b29c32037f9, and pending Chat 05 actual runningSup_monotone_and_path_le (do not submit before latter is Proved).

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.reflectedSup_right_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s => reflectedSup X s ω) (Set.Ici t) t := by sorry
