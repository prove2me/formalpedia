-- Prove2me | Theorems.Thm_BookProof_LorentzOrthochronous_isLorentz_neg
-- name    : BookProof.LorentzOrthochronous.isLorentz_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:35:46.655977+00:00
-- url     : https://prove2.me/theorems/fccd0f2a-fde6-4b7f-924d-bcea04a4b85f
-- title:
--   `BookProof.LorentzOrthochronous.isLorentz_neg` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : IsLorentz (-l)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzOrthochronous`.
--
--   `BookProof.LorentzOrthochronous.isLorentz_neg` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : IsLorentz (-l)
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzOrthochronous.isLorentz_neg`.

-- Generated from ChapterLorentzOrthochronous.lean — theorem BookProof.LorentzOrthochronous.isLorentz_neg
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup
open BookProof.LorentzOrthochronous



open Matrix
open BookProof.LorentzGroup

theorem BookProof.LorentzOrthochronous.isLorentz_neg {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    IsLorentz (-l) := by sorry
