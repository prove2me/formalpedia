-- Prove2me | Theorems.Thm_BookProof_LorentzOrthochronous_isPO_inv
-- name    : BookProof.LorentzOrthochronous.isPO_inv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:39:01.117975+00:00
-- url     : https://prove2.me/theorems/6f0540c3-300d-47af-a68e-07fe149d92b5
-- title:
--   `BookProof.LorentzOrthochronous.isPO_inv` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsProperOrthochronous l) : IsProperOrthochronous l⁻¹
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzOrthochronous`.
--
--   `BookProof.LorentzOrthochronous.isPO_inv` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsProperOrthochronous l) : IsProperOrthochronous l⁻¹
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzOrthochronous.isPO_inv`.

-- Generated from ChapterLorentzOrthochronous.lean — theorem BookProof.LorentzOrthochronous.isPO_inv
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup
open BookProof.LorentzOrthochronous



open Matrix
open BookProof.LorentzGroup

theorem BookProof.LorentzOrthochronous.isPO_inv {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsProperOrthochronous l) :
    IsProperOrthochronous l⁻¹ := by sorry
