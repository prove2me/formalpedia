-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
-- name    : AvramDividend.Classical.levy_runningSup_joint_time_path_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:26:44.185997+00:00
-- url     : https://prove2.me/theorems/ecfe330c-0715-46eb-8469-74c57473ccf7
-- title:
--   The genuine Lévy running supremum is jointly measurable in time and sample path
-- statement:
--   For any genuine spectrally negative Lévy process, the actual continuous-time running supremum is a Borel measurable function of the horizon and the sample path jointly, on the product of nonnegative time with the original sample-space measurable structure. This establishes measurable evaluation at independent exponential observation times.
-- source:
--   Proved runningSup_isDividendStrategy 8f7ae7d8-6651-454c-8d22-167256ac01b4 gives fixed-time adaptedness; Proved runningSup_right_continuous_actual 9faeaaa4-6933-425a-ac6d-88d7bf48aa56 gives right-continuous time sections; Proved rightContinuous_measurable_sections_joint_evaluation 8aafec11-d8a5-443c-9386-270a0d5c8a04 is the joint measurability theorem.

import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_actual
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem AvramDividend.Classical.levy_runningSup_joint_time_path_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun z : ℝ≥0 × Ω => runningSup X z.1 z.2) := by sorry
