-- Prove2me | Theorems.Thm_BookProof_LorentzGroup_lorentz_det_ne_zero
-- name    : BookProof.LorentzGroup.lorentz_det_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:35:15.515022+00:00
-- url     : https://prove2.me/theorems/e678b7ae-c985-4070-aa6f-2b5c53286ad9
-- title:
--   `BookProof.LorentzGroup.lorentz_det_ne_zero` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : l.det ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzGroup`.
--
--   `BookProof.LorentzGroup.lorentz_det_ne_zero` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : l.det ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzGroup.lorentz_det_ne_zero`.

-- Generated from ChapterLorentzGroup.lean — theorem BookProof.LorentzGroup.lorentz_det_ne_zero
import Mathlib
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup



open Matrix

theorem BookProof.LorentzGroup.lorentz_det_ne_zero {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    l.det ≠ 0 := by sorry
