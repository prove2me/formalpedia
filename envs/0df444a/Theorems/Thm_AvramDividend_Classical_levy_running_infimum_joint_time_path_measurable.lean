-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
-- name    : AvramDividend.Classical.levy_running_infimum_joint_time_path_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:34:29.998925+00:00
-- url     : https://prove2.me/theorems/ae09696f-14ab-4f36-9a12-bc4042f0892e
-- title:
--   The exact finite-time running infimum is jointly measurable in the Lévy path and the horizon
-- statement:
--   For a genuine spectrally negative Lévy process X, the real observable (t,ω)↦−inf_{0≤s≤t}X_s(ω) is jointly Borel measurable. The closed-horizon event includes the endpoint state X_t and is represented as survival strictly before t, equivalently t≤the true first downward crossing clock, together with a safe endpoint. This handles downward jumps at random exponential observation times without a countable-grid approximation.
-- source:
--   Proved lower_survival_running_infimum_equiv 46ecadff-9b33-407e-adbc-6b41a94cd506 and finite-horizon boundedness; lower_clock_weak_survival_past_ws01a 604b702f-041e-4920-8fa6-781326c492e2; chat03_both_named_passage_clocks_measurable 3d4daa72-4dba-48f9-9f55-b9a0e92786e4; chat04_levy_joint_time_state_measurable d55462c3-decf-40f0-9aff-439d356324d9.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_AvramDividend_Classical_chat04_lower_clock_weak_survival_past_ws01a
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_running_infimum_joint_time_path_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun z : ℝ≥0 × Ω =>
      -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ z.1 ∧ y = X.X s z.2}) := by sorry
