-- Prove2me | Theorems.Thm_BookProof_ChapterCPTHamiltonian_castMat_conjTranspose
-- name    : BookProof.ChapterCPTHamiltonian.castMat_conjTranspose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:22:21.451999+00:00
-- url     : https://prove2.me/theorems/efd6888b-c0d3-4503-b578-d42c6fd404e5
-- title:
--   `BookProof.ChapterCPTHamiltonian.castMat_conjTranspose` (M : Matrix (Fin 4) (Fin 4) ℤ) : ((Int.castRingHom ℂ).mapMatrix M)ᴴ = (Int.castRingHom ℂ).mapMatrix Mᵀ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCPTHamiltonian`.
--
--   `BookProof.ChapterCPTHamiltonian.castMat_conjTranspose` (M : Matrix (Fin 4) (Fin 4) ℤ) : ((Int.castRingHom ℂ).mapMatrix M)ᴴ = (Int.castRingHom ℂ).mapMatrix Mᵀ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCPTHamiltonian.castMat_conjTranspose`.

-- Generated from ChapterCPTHamiltonian.lean — theorem BookProof.ChapterCPTHamiltonian.castMat_conjTranspose
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterCPTHamiltonian.castMat_conjTranspose (M : Matrix (Fin 4) (Fin 4) ℤ) :
    ((Int.castRingHom ℂ).mapMatrix M)ᴴ = (Int.castRingHom ℂ).mapMatrix Mᵀ := by sorry
