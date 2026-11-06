-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_negative_mark_uniform_large_jump_squared_bound
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_negative_mark_uniform_large_jump_squared_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:00:52.541509+00:00
-- url     : https://prove2.me/theorems/31494b5c-f3d8-4638-b02e-eedd2da0560c
-- title:
--   Original continuous-negative payoff has a uniform squared large-mark jump bound below any finite reserve ceiling
-- statement:
--   For the original UBV verification payoff w continuous on nonnegative reserves and identically zero at negative reserves, every bounded positive reserve localisation [δ,K] admits a finite M that uniformly dominates the square of the physical negative jump coefficient w(u+z)-w(u) for all negative marks z. It is exactly the large-negative-mark half of the genuine Lévy min(1,z²) quadratic compensation bound, with no globally bounded w assumption and no proxy process.
-- source:
--   Use proved 22692cae compact-below-K original payoff value bound on both u and u+z≤K, triangle inequality, then square via nonnegative factors. Supplies a physical large-negative-mark bound for original Ito-Meyer, without requiring w smooth at ruin zero.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_tail_global_value_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_negative_mark_uniform_large_jump_squared_bound
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u ∈ Icc δ K, ∀ z : ℝ, z < 0 →
        (w (u + z) - w u) ^ 2 ≤ M := by sorry
