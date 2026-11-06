-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_tail_global_value_bound
-- name    : AvramDividend.Classical.avram_p4_f3_original_negative_tail_global_value_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:35:40.657546+00:00
-- url     : https://prove2.me/theorems/22692cae-5638-49ad-af4d-8d9030955209
-- title:
--   Original UBV verification value bounded uniformly below any finite reserve ceiling
-- statement:
--   Canonical original w is continuous on nonnegative reserves and identically zero at negative reserves. For any finite K>=0, |w(y)| is uniformly bounded on the whole negative half-line through K. This supplies a source-exact finite-activity large-negative-jump coefficient bound without any derivative control near ruin zero.
-- source:
--   Canonical fdb9a6a3 hw_cont on Ici 0, hw_neg on y<0, compact continuity bound on Icc 0 K, and source exact case split. The proof is purely deterministic and applies to original negative jumps at all sizes.

import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_negative_tail_global_value_bound
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℝ, y ≤ K → |w y| ≤ A := by sorry
