-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_semibounded_friedrichs_unique
-- name    : BookProof.FriedrichsCanonical.semibounded_friedrichs_unique
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T00:38:40.257595+00:00
-- url     : https://prove2.me/theorems/47a4758e-660f-4e96-a140-851c42315b31
-- title:
--   `BookProof.FriedrichsCanonical.semibounded_friedrichs_unique` (H : D →ₗ[ℂ] F) (hsym : SymmetricOn D H) (c : ℝ) (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ quadForm H x) (hdense : Dense
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.semibounded_friedrichs_unique` (H : D →ₗ[ℂ] F) (hsym : SymmetricOn D H) (c : ℝ) (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ quadForm H x) (hdense : Dense (D : Set F)) {Dom' : Submodule ℂ F} (A' : Dom' →ₗ[ℂ] F) (hA' : IsSemiboundedSelfAdjointExtension c H A') (hform : Dom' ≤ formDomain (shiftedPosSymOp H hsym c hbelow)) : Dom' = friedrichsDomain (shiftedPosSymOp H hsym c hbelow) ∧ ∀ (x : F) (hx : x ∈ Dom') (hx' : x ∈ friedrichsDomain (shiftedPosSymOp H hsym c hbelow)), A' ⟨x, hx⟩ = semiboundedFriedrichsOp H hsym c hbelow hdense ⟨x, hx'⟩
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.semibounded_friedrichs_unique`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.semibounded_friedrichs_unique
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {D : Submodule ℂ F}

theorem BookProof.FriedrichsCanonical.semibounded_friedrichs_unique (H : D →ₗ[ℂ] F) (hsym : SymmetricOn D H) (c : ℝ)
    (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ quadForm H x) (hdense : Dense (D : Set F))
    {Dom' : Submodule ℂ F} (A' : Dom' →ₗ[ℂ] F)
    (hA' : IsSemiboundedSelfAdjointExtension c H A')
    (hform : Dom' ≤ formDomain (shiftedPosSymOp H hsym c hbelow)) :
    Dom' = friedrichsDomain (shiftedPosSymOp H hsym c hbelow) ∧
      ∀ (x : F) (hx : x ∈ Dom')
        (hx' : x ∈ friedrichsDomain (shiftedPosSymOp H hsym c hbelow)),
        A' ⟨x, hx⟩ = semiboundedFriedrichsOp H hsym c hbelow hdense ⟨x, hx'⟩ := by sorry
