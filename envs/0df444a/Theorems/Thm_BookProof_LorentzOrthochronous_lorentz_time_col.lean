-- Prove2me | Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_time_col
-- name    : BookProof.LorentzOrthochronous.lorentz_time_col
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:36:47.20999+00:00
-- url     : https://prove2.me/theorems/22eca749-3251-4abc-80a7-e7881cbc0074
-- title:
--   `BookProof.LorentzOrthochronous.lorentz_time_col` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : (l 0 0) ^ 2 = 1 + (l 1 0) ^ 2 + (l 2 0) ^ 2 + (l 3 0) ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzOrthochronous`.
--
--   `BookProof.LorentzOrthochronous.lorentz_time_col` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : (l 0 0) ^ 2 = 1 + (l 1 0) ^ 2 + (l 2 0) ^ 2 + (l 3 0) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzOrthochronous.lorentz_time_col`.

-- Generated from ChapterLorentzOrthochronous.lean — theorem BookProof.LorentzOrthochronous.lorentz_time_col
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup
open BookProof.LorentzOrthochronous



open Matrix
open BookProof.LorentzGroup

theorem BookProof.LorentzOrthochronous.lorentz_time_col {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    (l 0 0) ^ 2 = 1 + (l 1 0) ^ 2 + (l 2 0) ^ 2 + (l 3 0) ^ 2 := by sorry
