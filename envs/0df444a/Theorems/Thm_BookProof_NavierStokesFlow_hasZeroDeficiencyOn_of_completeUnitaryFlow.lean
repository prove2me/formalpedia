-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_hasZeroDeficiencyOn_of_completeUnitaryFlow
-- name    : BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_completeUnitaryFlow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:20:38.746114+00:00
-- url     : https://prove2.me/theorems/119e3de0-75bf-4401-8334-dab7106a92be
-- title:
--   The Lean 4 theorem `hasZeroDeficiencyOn_of_completeUnitaryFlow` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasZeroDeficiencyOn_of_completeUnitaryFlow` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_completeUnitaryFlow
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_completeUnitaryFlow (D : Submodule ℂ F) (H : D →ₗ[ℂ] D)
    (U : ℝ → F → F) (hdense : Dense (D : Set F)) (hnorm : ∀ (t : ℝ) (v : F), ‖U t v‖ = ‖v‖)
    (hU0 : ∀ v : F, U 0 v = v) (hUD : ∀ (t : ℝ) (v : D), U t (v : F) ∈ D)
    (hderiv : ∀ (v : D) (t : ℝ),
      HasDerivAt (fun s => U s (v : F)) (Complex.I • (H ⟨U t (v : F), hUD t v⟩ : F)) t) :
    HasZeroDeficiencyOn D H := by sorry
