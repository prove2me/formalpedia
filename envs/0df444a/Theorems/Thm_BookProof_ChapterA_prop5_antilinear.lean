-- Prove2me | Theorems.Thm_BookProof_ChapterA_prop5_antilinear
-- name    : BookProof.ChapterA.prop5_antilinear
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:00:08.382994+00:00
-- url     : https://prove2.me/theorems/7b10aa41-b527-48c7-bbdc-c93bcabd23d8
-- title:
--   `BookProof.ChapterA.prop5_antilinear` (U : H₁ →ₗ⋆[ℂ] H₂) : (Function.Surjective U ∧ ∀ x, (inner ℂ (U x) (U x) : ℂ) = (inner ℂ x x : ℂ)) ↔ (Function.Surjective U ∧ ∀...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1Prop5`.
--
--   `BookProof.ChapterA.prop5_antilinear` (U : H₁ →ₗ⋆[ℂ] H₂) : (Function.Surjective U ∧ ∀ x, (inner ℂ (U x) (U x) : ℂ) = (inner ℂ x x : ℂ)) ↔ (Function.Surjective U ∧ ∀ x, (inner ℝ (U x) (U x) : ℝ) = (inner ℝ x x : ℝ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.prop5_antilinear`.

-- Generated from ChapterA1Prop5.lean — theorem BookProof.ChapterA.prop5_antilinear
import Mathlib
import Definitions.Def_ChapterA1Prop5
import Definitions.Def_ChapterA
open BookProof.ChapterA

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace





attribute [local instance] InnerProductSpace.rclikeToReal

theorem BookProof.ChapterA.prop5_antilinear (U : H₁ →ₗ⋆[ℂ] H₂) :
    (Function.Surjective U ∧ ∀ x, (inner ℂ (U x) (U x) : ℂ) = (inner ℂ x x : ℂ)) ↔
    (Function.Surjective U ∧ ∀ x, (inner ℝ (U x) (U x) : ℝ) = (inner ℝ x x : ℝ)) := by sorry
