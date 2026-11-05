-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_finite_source_marks_joint_tag_convergence
-- name    : AvramDividend.Classical.avram_p3_main_finite_source_marks_joint_tag_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:43:51.154735+00:00
-- url     : https://prove2.me/theorems/be1cd1dd-c45e-4b12-b430-7bb3f924f65e
-- title:
--   Finite original BV source marks have jointly convergent left and right mesh tags
-- statement:
--   For any fixed finite collection of actually selected original BV source-jump times, if the left and right physical-grid tags of each source time tend to that time, then both tags are jointly within any positive tolerance for all selected marks eventually. This is the finite exceptional-mark uniformisation demanded by P3-D/P3-C cell-placement obligation 3. The independent actual X source grid/tag construction and chronological endpoint membership remain separate obligations.
-- source:
--   P3D_P3C_INTERFACE_OBLIGATIONS_20261104.md, obligation 3; source-exact deterministic finite-index grid tag transport to actual original nonnegative time marks.

import Mathlib
open Filter
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_main_finite_source_marks_joint_tag_convergence
    {ι : Type*} (S : Finset ι) (t : ι → ℝ≥0)
    (leftTag rightTag : ℕ → ι → ℝ≥0)
    (hleft : ∀ i, Tendsto (fun n => leftTag n i) atTop (nhds (t i)))
    (hright : ∀ i, Tendsto (fun n => rightTag n i) atTop (nhds (t i)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ i ∈ S,
      dist (leftTag n i) (t i) < ε ∧
      dist (rightTag n i) (t i) < ε := by sorry
