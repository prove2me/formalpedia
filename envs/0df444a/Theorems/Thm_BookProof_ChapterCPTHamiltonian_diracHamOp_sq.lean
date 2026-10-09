-- Prove2me | Theorems.Thm_BookProof_ChapterCPTHamiltonian_diracHamOp_sq
-- name    : BookProof.ChapterCPTHamiltonian.diracHamOp_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:31:45.686978+00:00
-- url     : https://prove2.me/theorems/897f4a2c-2fc5-4638-af05-6997e6a45748
-- title:
--   `BookProof.ChapterCPTHamiltonian.diracHamOp_sq` (k : Fin 3 → ℝ) (m1 m2 : ℝ) : diracHamOp k m1 m2 * diracHamOp k m1 m2 = (-((∑ j : Fin 3, (k j : ℂ) ^ 2) + (m1 : ℂ) ^ 2 + (m2 : ℂ) ^
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCPTHamiltonian`.
--
--   `BookProof.ChapterCPTHamiltonian.diracHamOp_sq` (k : Fin 3 → ℝ) (m1 m2 : ℝ) : diracHamOp k m1 m2 * diracHamOp k m1 m2 = (-((∑ j : Fin 3, (k j : ℂ) ^ 2) + (m1 : ℂ) ^ 2 + (m2 : ℂ) ^ 2)) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCPTHamiltonian.diracHamOp_sq`.

-- Generated from ChapterCPTHamiltonian.lean — theorem BookProof.ChapterCPTHamiltonian.diracHamOp_sq
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterCPTHamiltonian


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterCPTHamiltonian.diracHamOp_sq (k : Fin 3 → ℝ) (m1 m2 : ℝ) :
    diracHamOp k m1 m2 * diracHamOp k m1 m2
      = (-((∑ j : Fin 3, (k j : ℂ) ^ 2) + (m1 : ℂ) ^ 2 + (m2 : ℂ) ^ 2))
          • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by sorry
