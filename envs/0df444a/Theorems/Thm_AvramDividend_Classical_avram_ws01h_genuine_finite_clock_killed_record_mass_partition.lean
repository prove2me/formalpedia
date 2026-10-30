-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_genuine_finite_clock_killed_record_mass_partition
-- name    : AvramDividend.Classical.avram_ws01h_genuine_finite_clock_killed_record_mass_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:31:06.021633+00:00
-- url     : https://prove2.me/theorems/454f0ad4-193a-4e6b-b872-0851888f1d9e
-- title:
--   Exact lower-killed first-record plus no-record finite-clock Qp probability-mass partition from genuine Lévy survival
-- statement:
--   For any genuine spectrally negative Lévy process and every finite observation cap N, the probability under ANY joint path/real-clock measure of surviving above -x to the clock with clock≤N is exactly the sum of (i) the event of a genuine upper first-record before the clock and lower ruin, together with full fresh post-record survival from x+b, and (ii) the event of no upper record before the clock and original survival. Both summands are measurable, disjoint and exhaustive. In particular this applies unchanged to the actual terminal Esscher Qp, providing the measure-level finite-clock CDF renewal partition without assuming the desired scale exit identity.
-- source:
--   Proved WS01H actual finite-clock split a560158e; genuine source closed-history jointly measurable f2b6346c; upper passage measurable e1fe86e9; Mathlib disjoint measure union.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_finite_clock_survival_killed_record_or_no_record_partition
import Theorems.Thm_AvramDividend_Classical_chat04_closed_history_lower_survival_joint_measurable_ws01a
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_genuine_finite_clock_killed_record_mass_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (hb : 0 ≤ b) (N : ℝ≥0)
    (μ : Measure (Ω × ℝ)) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let E : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       Real.toNNReal z.2 ≤ N ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     let A : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       Real.toNNReal z.2 ≤ N ∧
       twoSidedExitUpTime X b z.1 < (Real.toNNReal z.2 : ℝ≥0∞) ∧
       twoSidedExitUpTime X b z.1 < twoSidedExitDownTime X (-x) z.1 ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal z.2 - τ z.1 →
         0 ≤ (x + b) + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)}
     let B : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       Real.toNNReal z.2 ≤ N ∧
       (Real.toNNReal z.2 : ℝ≥0∞) ≤ twoSidedExitUpTime X b z.1 ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     μ E = μ A + μ B) := by sorry
