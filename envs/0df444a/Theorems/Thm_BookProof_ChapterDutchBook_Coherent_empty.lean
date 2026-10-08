-- Prove2me | Theorems.Thm_BookProof_ChapterDutchBook_Coherent_empty
-- name    : BookProof.ChapterDutchBook.Coherent.empty
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:08:12.027975+00:00
-- url     : https://prove2.me/theorems/e73aa06b-a6f6-471e-807b-6cfb0f1e4c5e
-- title:
--   `BookProof.ChapterDutchBook.Coherent.empty` {Pr : Finset Ω → ℝ} (h : Coherent Pr) : Pr (∅ : Finset Ω) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDutchBook`.
--
--   `BookProof.ChapterDutchBook.Coherent.empty` {Pr : Finset Ω → ℝ} (h : Coherent Pr) : Pr (∅ : Finset Ω) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDutchBook.Coherent.empty`.

-- Generated from ChapterDutchBook.lean — theorem BookProof.ChapterDutchBook.Coherent.empty
import Mathlib
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterDutchBook


open scoped BigOperators
open Finset


variable {Ω : Type*} [DecidableEq Ω]

theorem BookProof.ChapterDutchBook.Coherent.empty {Pr : Finset Ω → ℝ} (h : Coherent Pr) : Pr (∅ : Finset Ω) = 0 := by sorry
