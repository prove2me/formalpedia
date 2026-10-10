-- Prove2me | Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_inv_eq
-- name    : BookProof.LorentzOrthochronous.lorentz_inv_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:36:09.448522+00:00
-- url     : https://prove2.me/theorems/efabe3cb-3bc9-4b7e-94f9-e05fac3b9070
-- title:
--   `BookProof.LorentzOrthochronous.lorentz_inv_eq` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : l⁻¹ = eta * lᵀ * eta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzOrthochronous`.
--
--   `BookProof.LorentzOrthochronous.lorentz_inv_eq` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : l⁻¹ = eta * lᵀ * eta
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzOrthochronous.lorentz_inv_eq`.

-- Generated from ChapterLorentzOrthochronous.lean — theorem BookProof.LorentzOrthochronous.lorentz_inv_eq
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup
open BookProof.LorentzOrthochronous



open Matrix
open BookProof.LorentzGroup

theorem BookProof.LorentzOrthochronous.lorentz_inv_eq {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    l⁻¹ = eta * lᵀ * eta := by sorry
