-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_friedrichs_unique_selfAdjoint
-- name    : BookProof.FriedrichsCanonical.friedrichs_unique_selfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:38:33.656447+00:00
-- url     : https://prove2.me/theorems/428da1fd-37a6-4514-8982-eb15598bc824
-- title:
--   `BookProof.FriedrichsCanonical.friedrichs_unique_selfAdjoint` (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) {Dom' : Submodule ℂ F} (A' : Dom' →ₗ[ℂ] F) (hA' : IsPositiveSelfAdjo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.friedrichs_unique_selfAdjoint` (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) {Dom' : Submodule ℂ F} (A' : Dom' →ₗ[ℂ] F) (hA' : IsPositiveSelfAdjointExtension P.op A') (hform : Dom' ≤ formDomain P) : Dom' = friedrichsDomain P ∧ ∀ (x : F) (hx : x ∈ Dom') (hx' : x ∈ friedrichsDomain P), A' ⟨x, hx⟩ = friedrichsOp P hdense ⟨x, hx'⟩
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.friedrichs_unique_selfAdjoint`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.friedrichs_unique_selfAdjoint
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.FriedrichsCanonical.friedrichs_unique_selfAdjoint (P : PosSymOp F) (hdense : Dense (P.dom : Set F))
    {Dom' : Submodule ℂ F} (A' : Dom' →ₗ[ℂ] F)
    (hA' : IsPositiveSelfAdjointExtension P.op A') (hform : Dom' ≤ formDomain P) :
    Dom' = friedrichsDomain P ∧
      ∀ (x : F) (hx : x ∈ Dom') (hx' : x ∈ friedrichsDomain P),
        A' ⟨x, hx⟩ = friedrichsOp P hdense ⟨x, hx'⟩ := by sorry
