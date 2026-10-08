-- Prove2me | Theorems.Thm_BookProof_ChapterDutchBook_Coherent_additive
-- name    : BookProof.ChapterDutchBook.Coherent.additive
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:08:30.81198+00:00
-- url     : https://prove2.me/theorems/26698ad2-d136-4b24-a601-97e0609af918
-- title:
--   `BookProof.ChapterDutchBook.Coherent.additive` {Pr : Finset Ω → ℝ} (h : Coherent Pr) {A B : Finset Ω} (hAB : Disjoint A B) : Pr (A ∪ B) = Pr A + Pr B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDutchBook`.
--
--   `BookProof.ChapterDutchBook.Coherent.additive` {Pr : Finset Ω → ℝ} (h : Coherent Pr) {A B : Finset Ω} (hAB : Disjoint A B) : Pr (A ∪ B) = Pr A + Pr B
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDutchBook.Coherent.additive`.

-- Generated from ChapterDutchBook.lean — theorem BookProof.ChapterDutchBook.Coherent.additive
import Mathlib
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterDutchBook


open scoped BigOperators
open Finset


variable {Ω : Type*} [DecidableEq Ω]

theorem BookProof.ChapterDutchBook.Coherent.additive {Pr : Finset Ω → ℝ} (h : Coherent Pr)
    {A B : Finset Ω} (hAB : Disjoint A B) :
    Pr (A ∪ B) = Pr A + Pr B := by sorry
