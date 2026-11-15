-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a96_original_measurable_physical_jump_time_mark_enumeration_20261114
-- name    : AvramDividend.Classical.avram_a96_original_measurable_physical_jump_time_mark_enumeration_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:33:34.748497+00:00
-- url     : https://prove2.me/theorems/23b87552-4642-41fb-ab4f-d9530b0c82bf
-- title:
--   Original Lévy process has a measurable, injective physical jump-time and mark sequence covering all nonzero jumps
-- statement:
--   For an arbitrary original spectrally negative Lévy process, construct a countable measurable sequence of candidate jump times T_n, their measurable active masks A_n, and jointly measurable actual jump-mark random variables Y_n. Active candidates are genuine nonzero physical jumps; active times are injectively indexed; every positive-time actual jump appears with its exact mark. No auxiliary probability space or independent marks assumptions.
-- source:
--   Proved wave5_02a_actual_original_measurable_jump_enumeration and Proved wave4_04a_actual_levy_jumpmark_joint_measurable; compose joint mark evaluation with the graph of each measurable candidate time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a96_original_measurable_physical_jump_time_mark_enumeration_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ (T : ℕ → Ω → ℝ≥0) (A : ℕ → Set Ω)
      (Y : ℕ → Ω → ℝ),
      (∀ n, Measurable (T n)) ∧
      (∀ n, MeasurableSet (A n)) ∧
      (∀ n, Measurable (Y n)) ∧
      (∀ ω n, ω ∈ A n →
        0 < T n ω ∧
        Y n ω = X.X (T n ω) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) (T n ω) ∧
        Y n ω ≠ 0) ∧
      (∀ ω n m, ω ∈ A n → ω ∈ A m →
        T n ω = T m ω → n = m) ∧
      (∀ ω u, 0 < u →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
        ∃ n, ω ∈ A n ∧ T n ω = u ∧
          Y n ω =
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by sorry
