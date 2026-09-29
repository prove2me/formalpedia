-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_friedrichs_extension_of_semibounded
-- name    : BookProof.YangMillsFriedrichs.friedrichs_extension_of_semibounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:20:48.284469+00:00
-- url     : https://prove2.me/theorems/2933aedb-8946-4b27-ae9d-1f0f86e91d73
-- title:
--   The Lean 4 theorem `friedrichs_extension_of_semibounded` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `friedrichs_extension_of_semibounded` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.friedrichs_extension_of_semibounded
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}





















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFriedrichs.friedrichs_extension_of_semibounded {D : Submodule ℂ F} (H : D →ₗ[ℂ] F)
    (friedrichs : ∀ (D' : Submodule ℂ F) (H' : D' →ₗ[ℂ] F), Dense (D' : Set F) →
      SymmetricOn D' H' → (∀ x : D', 0 ≤ quadForm H' x) →
      ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsPositiveSelfAdjointExtension H' A)
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D H)
    (hpos : ∀ x : D, 0 ≤ quadForm H x) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsPositiveSelfAdjointExtension H A := by sorry
