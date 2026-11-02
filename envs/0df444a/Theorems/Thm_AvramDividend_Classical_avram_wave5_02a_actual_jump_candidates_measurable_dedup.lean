-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_jump_candidates_measurable_dedup
-- name    : AvramDividend.Classical.avram_wave5_02a_actual_jump_candidates_measurable_dedup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:34:45.265508+00:00
-- url     : https://prove2.me/theorems/46beafdc-e02a-4344-bd16-6c76ca667156
-- title:
--   Original source measurable candidate times admit measurable distinct jump filtering
-- statement:
--   For arbitrary measurable candidate times on the original sample space, retain those that are positive actual source jumps and have not appeared earlier. Every active set is measurable and active candidate times are pairwise distinct at each sample. Coverage of source jumps by the candidates is a separate obligation.
-- source:
--   Original joint Levy jump-mark measurability 9d68c5c2 and countable measurable set operations.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_actual_jump_candidates_measurable_dedup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℕ → Ω → ℝ≥0) (hT : ∀ n, Measurable (T n)) :
    let A : ℕ → Set Ω := fun n => {ω |
      0 < T n ω ∧
      X.X (T n ω) ω -
        Function.leftLim (fun u : ℝ≥0 => X.X u ω) (T n ω) ≠ 0 ∧
      ∀ m < n, T m ω ≠ T n ω}
    (∀ n, MeasurableSet (A n)) ∧
    (∀ ω n m, ω ∈ A n → ω ∈ A m → n ≠ m → T n ω ≠ T m ω) := by sorry
