-- Prove2me | Theorems.Thm_BookProof_ChapterA_AntiUnitary_comp_inner
-- name    : BookProof.ChapterA.AntiUnitary.comp_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T04:34:49.085449+00:00
-- url     : https://prove2.me/theorems/837ff1b0-e1dc-4c34-bd05-3233af33cee5
-- title:
--   `BookProof.ChapterA.AntiUnitary.comp_inner` (θ θ' : AntiUnitary V) (x y : V) : inner ℂ (θ' (θ x)) (θ' (θ y)) = inner ℂ x y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1`.
--
--   `BookProof.ChapterA.AntiUnitary.comp_inner` (θ θ' : AntiUnitary V) (x y : V) : inner ℂ (θ' (θ x)) (θ' (θ y)) = inner ℂ x y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.AntiUnitary.comp_inner`.

-- Generated from ChapterA1.lean — theorem BookProof.ChapterA.AntiUnitary.comp_inner
import Mathlib
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

theorem BookProof.ChapterA.AntiUnitary.comp_inner (θ θ' : AntiUnitary V) (x y : V) :
    inner ℂ (θ' (θ x)) (θ' (θ y)) = inner ℂ x y := by sorry
