-- Prove2me | Theorems.Thm_BookProof_Complexification_irreducible_iff_no_conj_subsystem
-- name    : BookProof.Complexification.irreducible_iff_no_conj_subsystem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:49:38.555987+00:00
-- url     : https://prove2.me/theorems/dc9a67c3-42df-4ceb-868d-1c8c625d283a
-- title:
--   `BookProof.Complexification.irreducible_iff_no_conj_subsystem` [CompleteSpace W] (M : System ℝ W) : M.IsIrreducible ↔ ∀ X : Submodule ℂ (Cx W), (cxSystem M).IsSubsystem X → (∀ x ∈
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1b`.
--
--   `BookProof.Complexification.irreducible_iff_no_conj_subsystem` [CompleteSpace W] (M : System ℝ W) : M.IsIrreducible ↔ ∀ X : Submodule ℂ (Cx W), (cxSystem M).IsSubsystem X → (∀ x ∈ X, Cx.cxConj x ∈ X) → X = ⊥ ∨ X = ⊤
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.irreducible_iff_no_conj_subsystem`.

-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.irreducible_iff_no_conj_subsystem
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_ChapterA
import Definitions.Def_Complexification
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.Complexification


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable [CompleteSpace W]

theorem BookProof.Complexification.irreducible_iff_no_conj_subsystem [CompleteSpace W] (M : System ℝ W) :
    M.IsIrreducible ↔
      ∀ X : Submodule ℂ (Cx W), (cxSystem M).IsSubsystem X →
        (∀ x ∈ X, Cx.cxConj x ∈ X) → X = ⊥ ∨ X = ⊤ := by sorry
