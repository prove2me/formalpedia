-- Prove2me | Theorems.Thm_BookProof_LorentzGroup_isLorentz_mul
-- name    : BookProof.LorentzGroup.isLorentz_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:34:09.860548+00:00
-- url     : https://prove2.me/theorems/a6c4c480-534b-4e0e-b4fd-80e0595292a3
-- title:
--   `BookProof.LorentzGroup.isLorentz_mul` {a b : Matrix (Fin 4) (Fin 4) ℝ} (ha : IsLorentz a) (hb : IsLorentz b) : IsLorentz (a * b)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzGroup`.
--
--   `BookProof.LorentzGroup.isLorentz_mul` {a b : Matrix (Fin 4) (Fin 4) ℝ} (ha : IsLorentz a) (hb : IsLorentz b) : IsLorentz (a * b)
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzGroup.isLorentz_mul`.

-- Generated from ChapterLorentzGroup.lean — theorem BookProof.LorentzGroup.isLorentz_mul
import Mathlib
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup



open Matrix

theorem BookProof.LorentzGroup.isLorentz_mul {a b : Matrix (Fin 4) (Fin 4) ℝ}
    (ha : IsLorentz a) (hb : IsLorentz b) : IsLorentz (a * b) := by sorry
