-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_finitely_marked_source_increment_vanish
-- name    : AvramDividend.Classical.avram_p3_main_public_finitely_marked_source_increment_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:31:47.870773+00:00
-- url     : https://prove2.me/theorems/81a61820-076d-4489-bbce-91f8158cad11
-- title:
--   Public original BV P3-D finite source negative-jump tail interface
-- statement:
--   Publicly importable source-identical replay of the accepted original bounded-variation negative-jump finite-tail or finite-mark bound; retains exact source jump magnitudes and finite-exclusion accounting without new process assumptions.
-- source:
--   Original accepted private P3-D AvramDividend.Classical.avram_p3_d_bvmesh_finitely_marked_original_jump_cells_vanish UUID 4a7cc66d-1ade-4501-b35c-579593747e4c, submission eb585a20-3624-4e76-aac2-e4a70843ea90, source SHA-256 3d7acabdc533cbb1524658b6ffc795f33418e60ad232900fd5a0b80985b3a375. Canonical stochastic P3 a19d8b28 requires publicly importable source-tail limits.

import Mathlib
open Filter
open scoped BigOperators

theorem AvramDividend.Classical.avram_p3_main_public_finitely_marked_source_increment_vanish
    {ι : Type*} (S : Finset ι) (c : ℕ → ι → ℝ)
    (hc : ∀ i ∈ S, Filter.Tendsto (fun k => c k i) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ∑ i ∈ S, |c k i|) Filter.atTop (nhds 0) := by sorry
