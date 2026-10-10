-- Prove2me | Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_time_row
-- name    : BookProof.LorentzOrthochronous.lorentz_time_row
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:36:40.724137+00:00
-- url     : https://prove2.me/theorems/5f46e475-bfbb-41ec-a70a-eca5cee3db15
-- title:
--   `BookProof.LorentzOrthochronous.lorentz_time_row` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : (l 0 0) ^ 2 = 1 + (l 0 1) ^ 2 + (l 0 2) ^ 2 + (l 0 3) ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzOrthochronous`.
--
--   `BookProof.LorentzOrthochronous.lorentz_time_row` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : (l 0 0) ^ 2 = 1 + (l 0 1) ^ 2 + (l 0 2) ^ 2 + (l 0 3) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzOrthochronous.lorentz_time_row`.

-- Generated from ChapterLorentzOrthochronous.lean — theorem BookProof.LorentzOrthochronous.lorentz_time_row
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup
open BookProof.LorentzOrthochronous



open Matrix
open BookProof.LorentzGroup

theorem BookProof.LorentzOrthochronous.lorentz_time_row {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    (l 0 0) ^ 2 = 1 + (l 0 1) ^ 2 + (l 0 2) ^ 2 + (l 0 3) ^ 2 := by sorry
