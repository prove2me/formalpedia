-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_nominal_cuts_geometry
-- name    : AvramDividend.Classical.avram_p2_l_mesh_uniform_nominal_cuts_geometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:58:36.676908+00:00
-- url     : https://prove2.me/theorems/df77f35c-924e-4ba1-b765-281e57356518
-- title:
--   Strictly increasing finite uniform real nominal partition with exact successor gaps
-- statement:
--   For a positive real cell length h, the finite nominal real mesh p(i)=A+i*h on indices Fin(n+1) is strictly increasing, has exact adjacent gap h, begins at A and ends at A+n*h. This finite-grid geometry is the bridge between Archimedean mesh fineness and order-preserving finite-jump-mark perturbations.

import Mathlib

theorem AvramDividend.Classical.avram_p2_l_mesh_uniform_nominal_cuts_geometry
    (n : ℕ) (A h : ℝ) (hh : 0 < h) :
    StrictMono (fun i : Fin (n + 1) => A + (i.val : ℝ) * h) ∧
    (∀ i : Fin n,
      (A + (i.succ.val : ℝ) * h) -
        (A + (i.castSucc.val : ℝ) * h) = h) ∧
    (A + ((0 : Fin (n + 1)).val : ℝ) * h) = A ∧
    (A + ((Fin.last n).val : ℝ) * h) = A + (n : ℝ) * h := by sorry
