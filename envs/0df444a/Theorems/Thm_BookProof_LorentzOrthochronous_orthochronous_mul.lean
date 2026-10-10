-- Prove2me | Theorems.Thm_BookProof_LorentzOrthochronous_orthochronous_mul
-- name    : BookProof.LorentzOrthochronous.orthochronous_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:36:52.489602+00:00
-- url     : https://prove2.me/theorems/52c3d471-6c98-4d62-8468-d733ea47e342
-- title:
--   `BookProof.LorentzOrthochronous.orthochronous_mul` {a b : Matrix (Fin 4) (Fin 4) ℝ} (ha : IsLorentz a) (hb : IsLorentz b) (h0a : 0 < a 0 0) (h0b : 0 < b 0 0) : 0 < (a * b) 0 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzOrthochronous`.
--
--   `BookProof.LorentzOrthochronous.orthochronous_mul` {a b : Matrix (Fin 4) (Fin 4) ℝ} (ha : IsLorentz a) (hb : IsLorentz b) (h0a : 0 < a 0 0) (h0b : 0 < b 0 0) : 0 < (a * b) 0 0
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzOrthochronous.orthochronous_mul`.

-- Generated from ChapterLorentzOrthochronous.lean — theorem BookProof.LorentzOrthochronous.orthochronous_mul
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup
open BookProof.LorentzOrthochronous



open Matrix
open BookProof.LorentzGroup

theorem BookProof.LorentzOrthochronous.orthochronous_mul {a b : Matrix (Fin 4) (Fin 4) ℝ}
    (ha : IsLorentz a) (hb : IsLorentz b) (h0a : 0 < a 0 0) (h0b : 0 < b 0 0) :
    0 < (a * b) 0 0 := by sorry
