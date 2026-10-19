-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_friedrichs_canonical
-- name    : BookProof.FriedrichsCanonical.friedrichs_canonical
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T00:37:55.948843+00:00
-- url     : https://prove2.me/theorems/9991b79c-d1fa-4d07-a043-0ec99cbf9e34
-- title:
--   `BookProof.FriedrichsCanonical.friedrichs_canonical` (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) {Dom' : Submodule ℂ F} (A' : Dom' →ₗ[ℂ] F) (hext : ∀ x : P.dom, ∃ h : (x : F)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.friedrichs_canonical` (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) {Dom' : Submodule ℂ F} (A' : Dom' →ₗ[ℂ] F) (hext : ∀ x : P.dom, ∃ h : (x : F) ∈ Dom', A' ⟨(x : F), h⟩ = P.op x) (hsym : SymmetricOn Dom' A') (hform : Dom' ≤ formDomain P) (x : F) (hx : x ∈ Dom') : ∃ h : x ∈ friedrichsDomain P, friedrichsOp P hdense ⟨x, h⟩ = A' ⟨x, hx⟩
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.friedrichs_canonical`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.friedrichs_canonical
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterQgOuterFockFarisLavine
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.QgOuterFockFL
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.FriedrichsCanonical.friedrichs_canonical (P : PosSymOp F) (hdense : Dense (P.dom : Set F))
    {Dom' : Submodule ℂ F} (A' : Dom' →ₗ[ℂ] F)
    (hext : ∀ x : P.dom, ∃ h : (x : F) ∈ Dom', A' ⟨(x : F), h⟩ = P.op x)
    (hsym : SymmetricOn Dom' A') (hform : Dom' ≤ formDomain P)
    (x : F) (hx : x ∈ Dom') :
    ∃ h : x ∈ friedrichsDomain P, friedrichsOp P hdense ⟨x, h⟩ = A' ⟨x, hx⟩ := by sorry
