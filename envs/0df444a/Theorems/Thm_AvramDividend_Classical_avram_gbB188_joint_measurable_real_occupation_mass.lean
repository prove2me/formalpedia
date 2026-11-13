-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB188_joint_measurable_real_occupation_mass
-- name    : AvramDividend.Classical.avram_gbB188_joint_measurable_real_occupation_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T19:03:52.039469+00:00
-- url     : https://prove2.me/theorems/a760f17b-c2b3-46e1-9e5e-ea3ed8009504
-- title:
--   Joint measurability of real-time path occupation mass at a variable level
-- statement:
--   If a stochastic real-time process Y is jointly measurable, its finite-horizon occupation mass of the moving singleton level y is measurable in (omega,y). This is the exact Fubini measurability prerequisite for exchanging path-a.e and level-a.e occupation statements in B187.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB188_joint_measurable_real_occupation_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Y : Ω → ℝ → ℝ)
    (hY : Measurable (fun z : Ω × ℝ => Y z.1 z.2))
    (n : ℕ) :
    Measurable (fun z : Ω × ℝ =>
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ Y z.1 t = z.2}) := by sorry
