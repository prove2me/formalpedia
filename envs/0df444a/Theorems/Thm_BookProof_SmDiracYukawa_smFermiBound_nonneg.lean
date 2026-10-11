-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_smFermiBound_nonneg
-- name    : BookProof.SmDiracYukawa.smFermiBound_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:52:22.810473+00:00
-- url     : https://prove2.me/theorems/9bf6bc27-7dab-4b61-b06f-dc9eb5e50c29
-- title:
--   `BookProof.SmDiracYukawa.smFermiBound_nonneg` (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : 0 ≤ smFermiBound hD M z
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.smFermiBound_nonneg` (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : 0 ≤ smFermiBound hD M z
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.smFermiBound_nonneg`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.smFermiBound_nonneg
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

theorem BookProof.SmDiracYukawa.smFermiBound_nonneg (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    0 ≤ smFermiBound hD M z := by sorry
