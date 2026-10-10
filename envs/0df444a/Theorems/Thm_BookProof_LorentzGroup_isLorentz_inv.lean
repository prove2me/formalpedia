-- Prove2me | Theorems.Thm_BookProof_LorentzGroup_isLorentz_inv
-- name    : BookProof.LorentzGroup.isLorentz_inv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:34:48.018524+00:00
-- url     : https://prove2.me/theorems/f856de6c-6e7c-4cd4-a0e0-b2d8280cca3f
-- title:
--   `BookProof.LorentzGroup.isLorentz_inv` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : IsLorentz l⁻¹
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzGroup`.
--
--   `BookProof.LorentzGroup.isLorentz_inv` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : IsLorentz l⁻¹
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzGroup.isLorentz_inv`.

-- Generated from ChapterLorentzGroup.lean — theorem BookProof.LorentzGroup.isLorentz_inv
import Mathlib
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup



open Matrix

theorem BookProof.LorentzGroup.isLorentz_inv {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    IsLorentz l⁻¹ := by sorry
