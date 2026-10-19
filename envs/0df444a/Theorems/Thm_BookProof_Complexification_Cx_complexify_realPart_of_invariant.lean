-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_complexify_realPart_of_invariant
-- name    : BookProof.Complexification.Cx.complexify_realPart_of_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:48:38.467+00:00
-- url     : https://prove2.me/theorems/723251a2-3e8b-44e7-9f7d-d27a35d745e2
-- title:
--   `BookProof.Complexification.Cx.complexify_realPart_of_invariant` {X : Submodule ℂ (Cx W)} (hX : ∀ x ∈ X, cxConj x ∈ X) : complexify (realPart X) = X
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1b`.
--
--   `BookProof.Complexification.Cx.complexify_realPart_of_invariant` {X : Submodule ℂ (Cx W)} (hX : ∀ x ∈ X, cxConj x ∈ X) : complexify (realPart X) = X
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.complexify_realPart_of_invariant`.

-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.complexify_realPart_of_invariant
import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_Complexification
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem BookProof.Complexification.Cx.complexify_realPart_of_invariant {X : Submodule ℂ (Cx W)}
    (hX : ∀ x ∈ X, cxConj x ∈ X) : complexify (realPart X) = X := by sorry
