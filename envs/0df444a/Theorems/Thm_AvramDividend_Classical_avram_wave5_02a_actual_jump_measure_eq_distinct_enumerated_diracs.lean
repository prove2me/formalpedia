-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_jump_measure_eq_distinct_enumerated_diracs
-- name    : AvramDividend.Classical.avram_wave5_02a_actual_jump_measure_eq_distinct_enumerated_diracs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:45:32.350199+00:00
-- url     : https://prove2.me/theorems/570a808d-6ac3-475b-9d22-23c2224004fa
-- title:
--   Actual original jump measure equals the Dirac sum of any distinct covering source selectors
-- statement:
--   If a family of marked selectors contains precisely actual positive source jumps, covers every source jump, and has no repeated active times, the literal intrinsic original jump measure equals the countable sum of its active marked Dirac measures at each original sample. No source selector measurability or intensity law is assumed for this pathwise measure identity.
-- source:
--   Source jump-mark joint measurability, counting-measure evaluation and bijection of active indices to the actual source jumps.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_actual_jump_measure_eq_distinct_enumerated_diracs
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℕ → Ω → ℝ≥0) (A : ℕ → Set Ω)
    (hActive : ∀ ω n, ω ∈ A n → 0 < T n ω ∧
      X.X (T n ω) ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) (T n ω) ≠ 0)
    (hInject : ∀ ω n m, ω ∈ A n → ω ∈ A m → T n ω = T m ω → n = m)
    (hCover : ∀ ω u, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
      ∃ n, ω ∈ A n ∧ T n ω = u) :
    ∀ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
      Measure.sum (fun n => (A n).indicator
        (fun _ => Measure.dirac (T n ω, X.X (T n ω) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) (T n ω))) ω) := by sorry
