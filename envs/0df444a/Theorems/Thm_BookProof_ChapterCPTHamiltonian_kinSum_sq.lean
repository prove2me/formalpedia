-- Prove2me | Theorems.Thm_BookProof_ChapterCPTHamiltonian_kinSum_sq
-- name    : BookProof.ChapterCPTHamiltonian.kinSum_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:31:12.034676+00:00
-- url     : https://prove2.me/theorems/83fb9db3-dad4-4bca-93f0-d2e43f552f4e
-- title:
--   `BookProof.ChapterCPTHamiltonian.kinSum_sq` (k : Fin 3 → ℝ) : (∑ j : Fin 3, (k j : ℂ) • Kin j) * (∑ j : Fin 3, (k j : ℂ) • Kin j) = (∑ j : Fin 3, (k j : ℂ) ^ 2) • (1 :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCPTHamiltonian`.
--
--   `BookProof.ChapterCPTHamiltonian.kinSum_sq` (k : Fin 3 → ℝ) : (∑ j : Fin 3, (k j : ℂ) • Kin j) * (∑ j : Fin 3, (k j : ℂ) • Kin j) = (∑ j : Fin 3, (k j : ℂ) ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCPTHamiltonian.kinSum_sq`.

-- Generated from ChapterCPTHamiltonian.lean — theorem BookProof.ChapterCPTHamiltonian.kinSum_sq
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterCPTHamiltonian.kinSum_sq (k : Fin 3 → ℝ) :
    (∑ j : Fin 3, (k j : ℂ) • Kin j) * (∑ j : Fin 3, (k j : ℂ) • Kin j)
      = (∑ j : Fin 3, (k j : ℂ) ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by sorry
