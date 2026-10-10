-- Prove2me | Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_time_sq_ge_one
-- name    : BookProof.LorentzOrthochronous.lorentz_time_sq_ge_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:36:41.440983+00:00
-- url     : https://prove2.me/theorems/ff3ad995-2e45-484c-8afb-49cbb9bbd2c2
-- title:
--   `BookProof.LorentzOrthochronous.lorentz_time_sq_ge_one` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : 1 ≤ (l 0 0) ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzOrthochronous`.
--
--   `BookProof.LorentzOrthochronous.lorentz_time_sq_ge_one` {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) : 1 ≤ (l 0 0) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzOrthochronous.lorentz_time_sq_ge_one`.

-- Generated from ChapterLorentzOrthochronous.lean — theorem BookProof.LorentzOrthochronous.lorentz_time_sq_ge_one
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup
open BookProof.LorentzOrthochronous



open Matrix
open BookProof.LorentzGroup

theorem BookProof.LorentzOrthochronous.lorentz_time_sq_ge_one {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    1 ≤ (l 0 0) ^ 2 := by sorry
