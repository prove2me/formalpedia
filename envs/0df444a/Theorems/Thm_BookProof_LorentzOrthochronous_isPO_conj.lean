-- Prove2me | Theorems.Thm_BookProof_LorentzOrthochronous_isPO_conj
-- name    : BookProof.LorentzOrthochronous.isPO_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:37:43.010217+00:00
-- url     : https://prove2.me/theorems/ef2f24e3-edcd-4f7f-b970-35fbef6c9493
-- title:
--   `BookProof.LorentzOrthochronous.isPO_conj` {g s : Matrix (Fin 4) (Fin 4) ℝ} (hg : IsLorentz g) (hs : IsProperOrthochronous s) : IsProperOrthochronous (g * s * g⁻¹)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzOrthochronous`.
--
--   `BookProof.LorentzOrthochronous.isPO_conj` {g s : Matrix (Fin 4) (Fin 4) ℝ} (hg : IsLorentz g) (hs : IsProperOrthochronous s) : IsProperOrthochronous (g * s * g⁻¹)
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzOrthochronous.isPO_conj`.

-- Generated from ChapterLorentzOrthochronous.lean — theorem BookProof.LorentzOrthochronous.isPO_conj
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup
open BookProof.LorentzOrthochronous



open Matrix
open BookProof.LorentzGroup

theorem BookProof.LorentzOrthochronous.isPO_conj {g s : Matrix (Fin 4) (Fin 4) ℝ}
    (hg : IsLorentz g) (hs : IsProperOrthochronous s) :
    IsProperOrthochronous (g * s * g⁻¹) := by sorry
