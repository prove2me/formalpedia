-- Prove2me | Theorems.Thm_BookProof_LorentzOrthochronous_isPO_mul
-- name    : BookProof.LorentzOrthochronous.isPO_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:37:21.016737+00:00
-- url     : https://prove2.me/theorems/ace077f2-7f91-49a9-b3b4-b8d562aa1944
-- title:
--   `BookProof.LorentzOrthochronous.isPO_mul` {a b : Matrix (Fin 4) (Fin 4) ℝ} (ha : IsProperOrthochronous a) (hb : IsProperOrthochronous b) : IsProperOrthochronous (a * b)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzOrthochronous`.
--
--   `BookProof.LorentzOrthochronous.isPO_mul` {a b : Matrix (Fin 4) (Fin 4) ℝ} (ha : IsProperOrthochronous a) (hb : IsProperOrthochronous b) : IsProperOrthochronous (a * b)
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzOrthochronous.isPO_mul`.

-- Generated from ChapterLorentzOrthochronous.lean — theorem BookProof.LorentzOrthochronous.isPO_mul
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup
open BookProof.LorentzOrthochronous



open Matrix
open BookProof.LorentzGroup

theorem BookProof.LorentzOrthochronous.isPO_mul {a b : Matrix (Fin 4) (Fin 4) ℝ}
    (ha : IsProperOrthochronous a) (hb : IsProperOrthochronous b) :
    IsProperOrthochronous (a * b) := by sorry
