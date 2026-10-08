-- Prove2me | Theorems.Thm_BookProof_ChapterA_prop5
-- name    : BookProof.ChapterA.prop5
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T04:39:36.683785+00:00
-- url     : https://prove2.me/theorems/d077a934-caec-4a29-a6e5-6e5cc90a0c71
-- title:
--   `BookProof.ChapterA.prop5` (U : H₁ → H₂) : (Function.Surjective U ∧ ∀ x, (inner ℂ (U x) (U x) : ℂ) = (inner ℂ x x : ℂ)) ↔ (Function.Surjective U ∧ ∀ x, (inner ℝ (U x) (U...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1Prop5`.
--
--   `BookProof.ChapterA.prop5` (U : H₁ → H₂) : (Function.Surjective U ∧ ∀ x, (inner ℂ (U x) (U x) : ℂ) = (inner ℂ x x : ℂ)) ↔ (Function.Surjective U ∧ ∀ x, (inner ℝ (U x) (U x) : ℝ) = (inner ℝ x x : ℝ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.prop5`.

-- Generated from ChapterA1Prop5.lean — theorem BookProof.ChapterA.prop5
import Mathlib
import Definitions.Def_ChapterA1Prop5
import Definitions.Def_ChapterA
open BookProof.ChapterA

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace





attribute [local instance] InnerProductSpace.rclikeToReal

theorem BookProof.ChapterA.prop5 (U : H₁ → H₂) :
    (Function.Surjective U ∧ ∀ x, (inner ℂ (U x) (U x) : ℂ) = (inner ℂ x x : ℂ)) ↔
    (Function.Surjective U ∧ ∀ x, (inner ℝ (U x) (U x) : ℝ) = (inner ℝ x x : ℝ)) := by sorry
