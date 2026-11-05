-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_nonzero_finite_marks_positive_cutoff
-- name    : AvramDividend.Classical.avram_p3_main_public_nonzero_finite_marks_positive_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:37:51.179674+00:00
-- url     : https://prove2.me/theorems/b65f55e6-f0bf-41d8-88f3-e144d32c1a42
-- title:
--   Public source-exact finite nonzero original jump mark cutoff bridge
-- statement:
--   Source-identical public replay of the already-Proved original BV finite-mark positive cut-off or zero-mark removal lemma, needed for the true epsilon-small original-jump tail convergence while retaining the actual source jump-time index.
-- source:
--   Original accepted private AvramDividend.Classical.avram_p3_d_bvmesh_finite_nonzero_original_marks_positive_cutoff, UUID 182e334a-09ce-4e82-8473-7dd10b6ecdc1, submission 4a4aebec-4795-4e91-8cfa-68e4fed79c54, source SHA-256 f6db3d7c8f136389e123141d5e8db8ce05bc16b4f2d0d5b4c25304012688e022; P3-D source interface obligations 5 and original P3 a19d8b28.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_p3_main_public_nonzero_finite_marks_positive_cutoff
    {ι : Type*} (S : Finset ι) (j : ι → ℝ)
    (hS : ∀ i ∈ S, j i ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ S, δ ≤ |j i| := by sorry
