-- Prove2me | Theorems.Thm_BookProof_ChapterA3_spinorInv_conj_mgamma
-- name    : BookProof.ChapterA3.spinorInv_conj_mgamma
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:55:45.916269+00:00
-- url     : https://prove2.me/theorems/6a19855f-de88-48da-9b4c-6954ed6258fd
-- title:
--   `BookProof.ChapterA3.spinorInv_conj_mgamma` (T : Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) : SpinorInv T * mgamma μ * Spinor T = ∑ ν, UpsilonC T ν μ • mgamma ν
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3i`.
--
--   `BookProof.ChapterA3.spinorInv_conj_mgamma` (T : Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) : SpinorInv T * mgamma μ * Spinor T = ∑ ν, UpsilonC T ν μ • mgamma ν
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.spinorInv_conj_mgamma`.

-- Generated from ChapterA3i.lean — theorem BookProof.ChapterA3.spinorInv_conj_mgamma
import Mathlib
import Definitions.Def_ChapterA3i
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.spinorInv_conj_mgamma (T : Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) :
    SpinorInv T * mgamma μ * Spinor T = ∑ ν, UpsilonC T ν μ • mgamma ν := by sorry
