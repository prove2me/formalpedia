-- Prove2me | Theorems.Thm_BookProof_ChapterDutchBook_coherent_iff_exists_prob
-- name    : BookProof.ChapterDutchBook.coherent_iff_exists_prob
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:09:12.014821+00:00
-- url     : https://prove2.me/theorems/4f079baa-cf48-4b7a-878a-7f7d138b4aad
-- title:
--   `BookProof.ChapterDutchBook.coherent_iff_exists_prob` [Fintype Ω] (Pr : Finset Ω → ℝ) : Coherent Pr ↔ ∃ p : Ω → ℝ, IsProb p ∧ Represents Pr p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDutchBook`.
--
--   `BookProof.ChapterDutchBook.coherent_iff_exists_prob` [Fintype Ω] (Pr : Finset Ω → ℝ) : Coherent Pr ↔ ∃ p : Ω → ℝ, IsProb p ∧ Represents Pr p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDutchBook.coherent_iff_exists_prob`.

-- Generated from ChapterDutchBook.lean — theorem BookProof.ChapterDutchBook.coherent_iff_exists_prob
import Mathlib
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterDutchBook


open scoped BigOperators
open Finset


variable {Ω : Type*} [DecidableEq Ω]

theorem BookProof.ChapterDutchBook.coherent_iff_exists_prob [Fintype Ω] (Pr : Finset Ω → ℝ) :
    Coherent Pr ↔ ∃ p : Ω → ℝ, IsProb p ∧ Represents Pr p := by sorry
