-- Prove2me | Theorems.Thm_BookProof_EsaClosure_positiveExtension_eq_closure_of_esa
-- name    : BookProof.EsaClosure.positiveExtension_eq_closure_of_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:21:30.420979+00:00
-- url     : https://prove2.me/theorems/722fe28a-1ef4-4ca0-ac5d-7b6c1d3ea944
-- title:
--   The Lean 4 theorem `positiveExtension_eq_closure_of_esa` in the `ChapterEsaClosure` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `positiveExtension_eq_closure_of_esa` in the `ChapterEsaClosure` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterEsaClosure.lean

-- Generated from ChapterEsaClosure.lean — theorem BookProof.EsaClosure.positiveExtension_eq_closure_of_esa
import Mathlib
import Definitions.Def_ChapterEsaClosure
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterSirkBandLedger
open BookProof.EsaClosure



open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




variable [CompleteSpace F]

theorem BookProof.EsaClosure.positiveExtension_eq_closure_of_esa {Dom : Submodule ℂ F} {T : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T)
    (hesa : EssentiallySelfAdjointOn D T) (hA : IsPositiveSelfAdjointExtension T A) :
    Dom = clDom T ∧ ∀ (x : F) (h : x ∈ Dom) (h' : x ∈ clDom T),
      A ⟨x, h⟩ = clExt T hdense hsym ⟨x, h'⟩ := by sorry
