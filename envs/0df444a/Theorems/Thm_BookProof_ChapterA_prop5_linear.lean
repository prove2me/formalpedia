-- Prove2me | Theorems.Thm_BookProof_ChapterA_prop5_linear
-- name    : BookProof.ChapterA.prop5_linear
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T04:39:59.854173+00:00
-- url     : https://prove2.me/theorems/2752bdf2-3808-45e7-8e59-04be8a2f0fb7
-- title:
--   `BookProof.ChapterA.prop5_linear` (U : H₁ →ₗ[ℂ] H₂) : (Function.Surjective U ∧ ∀ x, (inner ℂ (U x) (U x) : ℂ) = (inner ℂ x x : ℂ)) ↔ (Function.Surjective U ∧ ∀ x,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1Prop5`.
--
--   `BookProof.ChapterA.prop5_linear` (U : H₁ →ₗ[ℂ] H₂) : (Function.Surjective U ∧ ∀ x, (inner ℂ (U x) (U x) : ℂ) = (inner ℂ x x : ℂ)) ↔ (Function.Surjective U ∧ ∀ x, (inner ℝ (U x) (U x) : ℝ) = (inner ℝ x x : ℝ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.prop5_linear`.

-- Generated from ChapterA1Prop5.lean — theorem BookProof.ChapterA.prop5_linear
import Mathlib
import Definitions.Def_ChapterA1Prop5
import Definitions.Def_ChapterA
open BookProof.ChapterA

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace





attribute [local instance] InnerProductSpace.rclikeToReal

theorem BookProof.ChapterA.prop5_linear (U : H₁ →ₗ[ℂ] H₂) :
    (Function.Surjective U ∧ ∀ x, (inner ℂ (U x) (U x) : ℂ) = (inner ℂ x x : ℂ)) ↔
    (Function.Surjective U ∧ ∀ x, (inner ℝ (U x) (U x) : ℝ) = (inner ℝ x x : ℝ)) := by sorry
