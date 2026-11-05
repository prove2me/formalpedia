-- Prove2me | Theorems.Thm_BookProof_RelationShiftInvert_unitaryU_eq_of_invCLM_eq
-- name    : BookProof.RelationShiftInvert.unitaryU_eq_of_invCLM_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T22:58:59.00898+00:00
-- url     : https://prove2.me/theorems/6a944393-b901-47aa-8406-4ed6e3ae071c
-- title:
--   `BookProof.RelationShiftInvert.unitaryU_eq_of_invCLM_eq` (hT₁ : IsNonnegSelfAdjoint T₁) (hT₂ : IsNonnegSelfAdjoint T₂) (hsv₁ : ∀ w : F, ((0 : F), w) ∈ T₁ → w = 0) (hsv₂ : ∀...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRelationShiftInvert`.
--
--   `BookProof.RelationShiftInvert.unitaryU_eq_of_invCLM_eq` (hT₁ : IsNonnegSelfAdjoint T₁) (hT₂ : IsNonnegSelfAdjoint T₂) (hsv₁ : ∀ w : F, ((0 : F), w) ∈ T₁ → w = 0) (hsv₂ : ∀ w : F, ((0 : F), w) ∈ T₂ → w = 0) (heq : invCLM hT₁ = invCLM hT₂) (t : ℝ) : unitaryU hT₁ hsv₁ t = unitaryU hT₂ hsv₂ t
--
--   Formalization note: Lean 4 identifier `BookProof.RelationShiftInvert.unitaryU_eq_of_invCLM_eq`.

-- Generated from ChapterRelationShiftInvert.lean — theorem BookProof.RelationShiftInvert.unitaryU_eq_of_invCLM_eq
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterNonnegSquareRoot
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegUnitaryGroup
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterRelationShiftInvert



open BookProof.PositiveSquareRoot
open BookProof.HashimotoShiftInvert
open BookProof.NonnegUnitaryGroup

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T T₁ T₂ : Submodule ℂ (F × F)}

theorem BookProof.RelationShiftInvert.unitaryU_eq_of_invCLM_eq (hT₁ : IsNonnegSelfAdjoint T₁) (hT₂ : IsNonnegSelfAdjoint T₂)
    (hsv₁ : ∀ w : F, ((0 : F), w) ∈ T₁ → w = 0) (hsv₂ : ∀ w : F, ((0 : F), w) ∈ T₂ → w = 0)
    (heq : invCLM hT₁ = invCLM hT₂) (t : ℝ) :
    unitaryU hT₁ hsv₁ t = unitaryU hT₂ hsv₂ t := by sorry
