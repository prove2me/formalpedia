-- Prove2me | Theorems.Thm_BookProof_LorentzOrthochronous_isLorentz_mul_eta_transpose
-- name    : BookProof.LorentzOrthochronous.isLorentz_mul_eta_transpose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:36:33.977981+00:00
-- url     : https://prove2.me/theorems/a3a40a77-66d5-401c-95b2-ec91dd7bfbb2
-- title:
--   `BookProof.LorentzOrthochronous.isLorentz_mul_eta_transpose` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : l * eta * lᵀ = eta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzOrthochronous`.
--
--   `BookProof.LorentzOrthochronous.isLorentz_mul_eta_transpose` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : l * eta * lᵀ = eta
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzOrthochronous.isLorentz_mul_eta_transpose`.

-- Generated from ChapterLorentzOrthochronous.lean — theorem BookProof.LorentzOrthochronous.isLorentz_mul_eta_transpose
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup
open BookProof.LorentzOrthochronous



open Matrix
open BookProof.LorentzGroup

theorem BookProof.LorentzOrthochronous.isLorentz_mul_eta_transpose {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    l * eta * lᵀ = eta := by sorry
