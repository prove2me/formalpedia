-- Prove2me | solution 1 for mme_dwz_q6_grade_one_coord_leftGrade
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:53:48.521091+00:00
-- url     : https://prove2.me/submissions/77a21488-1c37-45d4-8531-7081547d9cf5

import Definitions.Def_mme_dwz_q6_grade_one_coord_data

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem solution
    (p : LiftedCoarsePair.{u} 6 1) :
    p.leftGrade =
      Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
        (fun _ : Fin 6 ↦ (1 : Fin 3)) (dwzQ6GradeOneCoord p) := by
  rcases p with ⟨⟨⟨a, b⟩, hp⟩⟩
  change cwSquareCoordGrade 6 a =
    Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
      (fun _ : Fin 6 ↦ (1 : Fin 3))
      (if a.val = 0 then
        Sum.inl (Fin.ofNat 6 (b.val - 1))
      else
        Sum.inr (Fin.ofNat 6 (a.val - 1)))
  fin_cases a <;> fin_cases b <;>
    simp [cwSquarePairGrade, cwSquareCoordGrade] at hp ⊢
