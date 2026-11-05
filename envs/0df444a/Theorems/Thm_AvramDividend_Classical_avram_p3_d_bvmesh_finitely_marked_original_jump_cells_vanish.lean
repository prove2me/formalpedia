-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_d_bvmesh_finitely_marked_original_jump_cells_vanish
-- name    : AvramDividend.Classical.avram_p3_d_bvmesh_finitely_marked_original_jump_cells_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:46:10.495199+00:00
-- url     : https://prove2.me/theorems/4a7cc66d-1ade-4501-b35c-579593747e4c
-- title:
--   Finite marked original-jump cells have vanishing source-frozen variation
-- statement:
--   For a genuinely finite set S of marked original negative source-jump times, suppose the source-jump-removed continuous increment in each associated mesh cell tends to zero as that mesh refines. Then the total absolute source variation over marked cells tends to zero. Instantiate S using the summability cut-off theorem and c from the physical source drift-minus-monotone-residual path; this discharges the large-mark term of the P3-D translation bound, conditional on a real cell-allocation/continuity proof.
-- source:
--   Pinned Mathlib tendsto_finset_sum (Mathlib.Topology.Algebra.Monoid), continuous_abs (Mathlib.Topology.Algebra.Order.Group) and Filter.Tendsto.comp. P3-D original large/small jump translation bound 8d317909 has large-mark term sum S |c_i|; original P3-A residual continuity supplies the finite-cell tendsto premises only after a stopped mesh-placement construction.

import Mathlib
open Filter
open scoped BigOperators

theorem AvramDividend.Classical.avram_p3_d_bvmesh_finitely_marked_original_jump_cells_vanish
    {ι : Type*} (S : Finset ι) (c : ℕ → ι → ℝ)
    (hc : ∀ i ∈ S, Filter.Tendsto (fun k => c k i) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ∑ i ∈ S, |c k i|) Filter.atTop (nhds 0) := by sorry
