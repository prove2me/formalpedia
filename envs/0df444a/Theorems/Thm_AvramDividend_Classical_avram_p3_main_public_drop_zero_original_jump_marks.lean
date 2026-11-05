-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_drop_zero_original_jump_marks
-- name    : AvramDividend.Classical.avram_p3_main_public_drop_zero_original_jump_marks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:37:52.296866+00:00
-- url     : https://prove2.me/theorems/80743a61-81ee-435f-9664-9b90bad6e705
-- title:
--   Public source-exact finite nonzero original jump mark cutoff bridge
-- statement:
--   Source-identical public replay of the already-Proved original BV finite-mark positive cut-off or zero-mark removal lemma, needed for the true epsilon-small original-jump tail convergence while retaining the actual source jump-time index.
-- source:
--   Original accepted private AvramDividend.Classical.avram_p3_d_bvmesh_finite_exclusion_drop_zero_original_marks, UUID cd2bddc4-70cb-4278-9890-163220973e58, submission d9bebea1-6f69-4b4a-ae0a-9b0001419053, source SHA-256 e91d715f842d70e227473f131d315ccf697d4bfff7345df3c59819b30cedd38e; P3-D source interface obligations 5 and original P3 a19d8b28.

import Mathlib
open Filter Set
open scoped BigOperators

theorem AvramDividend.Classical.avram_p3_main_public_drop_zero_original_jump_marks
    {ι : Type*} [DecidableEq ι] (j : ι → ℝ) (S : Finset ι) :
    ∃ T : Finset ι, (∀ i ∈ T, j i ≠ 0) ∧
      (∑' i : ι, if i ∈ T then 0 else |j i|) =
        (∑' i : ι, if i ∈ S then 0 else |j i|) := by sorry
