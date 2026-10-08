-- Prove2me | Theorems.Thm_BookProof_ChapterCPTHamiltonian_kinSum_conjTranspose
-- name    : BookProof.ChapterCPTHamiltonian.kinSum_conjTranspose
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:31:36.447974+00:00
-- url     : https://prove2.me/theorems/6d911594-a73f-4339-b195-9f648f7fb058
-- title:
--   `BookProof.ChapterCPTHamiltonian.kinSum_conjTranspose` (k : Fin 3 → ℝ) : (∑ j : Fin 3, (k j : ℂ) • Kin j)ᴴ = ∑ j : Fin 3, (k j : ℂ) • Kin j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCPTHamiltonian`.
--
--   `BookProof.ChapterCPTHamiltonian.kinSum_conjTranspose` (k : Fin 3 → ℝ) : (∑ j : Fin 3, (k j : ℂ) • Kin j)ᴴ = ∑ j : Fin 3, (k j : ℂ) • Kin j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCPTHamiltonian.kinSum_conjTranspose`.

-- Generated from ChapterCPTHamiltonian.lean — theorem BookProof.ChapterCPTHamiltonian.kinSum_conjTranspose
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterCPTHamiltonian.kinSum_conjTranspose (k : Fin 3 → ℝ) :
    (∑ j : Fin 3, (k j : ℂ) • Kin j)ᴴ = ∑ j : Fin 3, (k j : ℂ) • Kin j := by sorry
