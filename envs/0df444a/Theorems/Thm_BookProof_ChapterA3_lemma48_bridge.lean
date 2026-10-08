-- Prove2me | Theorems.Thm_BookProof_ChapterA3_lemma48_bridge
-- name    : BookProof.ChapterA3.lemma48_bridge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:55:48.26498+00:00
-- url     : https://prove2.me/theorems/ee3c52b7-2168-4353-8372-91c735553b8b
-- title:
--   `BookProof.ChapterA3.lemma48_bridge` (T : Matrix (Fin 2) (Fin 2) ℂ) (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) (μ : Fin 4) : (Spinor T)⁻¹ * mgamma μ * Spinor T = ∑ ν, UpsilonC T ν
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3i`.
--
--   `BookProof.ChapterA3.lemma48_bridge` (T : Matrix (Fin 2) (Fin 2) ℂ) (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) (μ : Fin 4) : (Spinor T)⁻¹ * mgamma μ * Spinor T = ∑ ν, UpsilonC T ν μ • mgamma ν
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.lemma48_bridge`.

-- Generated from ChapterA3i.lean — theorem BookProof.ChapterA3.lemma48_bridge
import Mathlib
import Definitions.Def_ChapterA3i
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.lemma48_bridge (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) (μ : Fin 4) :
    (Spinor T)⁻¹ * mgamma μ * Spinor T = ∑ ν, UpsilonC T ν μ • mgamma ν := by sorry
