-- Prove2me | Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_time_ne_zero
-- name    : BookProof.LorentzOrthochronous.lorentz_time_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:36:48.333167+00:00
-- url     : https://prove2.me/theorems/03f16856-be5d-4c97-b04e-26c644ecb043
-- title:
--   `BookProof.LorentzOrthochronous.lorentz_time_ne_zero` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : l 0 0 ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzOrthochronous`.
--
--   `BookProof.LorentzOrthochronous.lorentz_time_ne_zero` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : l 0 0 ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzOrthochronous.lorentz_time_ne_zero`.

-- Generated from ChapterLorentzOrthochronous.lean — theorem BookProof.LorentzOrthochronous.lorentz_time_ne_zero
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup
open BookProof.LorentzOrthochronous



open Matrix
open BookProof.LorentzGroup

theorem BookProof.LorentzOrthochronous.lorentz_time_ne_zero {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    l 0 0 ≠ 0 := by sorry
