-- Prove2me | Theorems.Thm_BookProof_LorentzGroup_lorentz_det_sq_one
-- name    : BookProof.LorentzGroup.lorentz_det_sq_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:34:20.426297+00:00
-- url     : https://prove2.me/theorems/4598fa23-0e84-4a82-aa5f-391bd749d529
-- title:
--   `BookProof.LorentzGroup.lorentz_det_sq_one` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : l.det ^ 2 = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzGroup`.
--
--   `BookProof.LorentzGroup.lorentz_det_sq_one` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : l.det ^ 2 = 1
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzGroup.lorentz_det_sq_one`.

-- Generated from ChapterLorentzGroup.lean — theorem BookProof.LorentzGroup.lorentz_det_sq_one
import Mathlib
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup



open Matrix

theorem BookProof.LorentzGroup.lorentz_det_sq_one {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    l.det ^ 2 = 1 := by sorry
