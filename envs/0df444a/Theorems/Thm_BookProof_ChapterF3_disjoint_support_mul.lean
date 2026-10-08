-- Prove2me | Theorems.Thm_BookProof_ChapterF3_disjoint_support_mul
-- name    : BookProof.ChapterF3.disjoint_support_mul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:48:05.873244+00:00
-- url     : https://prove2.me/theorems/83fd0c93-9785-48cc-a0ce-926f6fe950cc
-- title:
--   `BookProof.ChapterF3.disjoint_support_mul` {α : Type*} (f g : α → ℂ) (h : Disjoint (Function.support f) (Function.support g)) : f * g = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF3`.
--
--   `BookProof.ChapterF3.disjoint_support_mul` {α : Type*} (f g : α → ℂ) (h : Disjoint (Function.support f) (Function.support g)) : f * g = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF3.disjoint_support_mul`.

-- Generated from ChapterF3.lean — theorem BookProof.ChapterF3.disjoint_support_mul
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3


open scoped BigOperators
open Polynomial


noncomputable section

theorem BookProof.ChapterF3.disjoint_support_mul {α : Type*} (f g : α → ℂ)
    (h : Disjoint (Function.support f) (Function.support g)) : f * g = 0 := by sorry
