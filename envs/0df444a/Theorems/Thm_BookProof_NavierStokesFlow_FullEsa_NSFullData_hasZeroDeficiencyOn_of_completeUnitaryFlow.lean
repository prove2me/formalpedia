-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_NSFullData_hasZeroDeficiencyOn_of_completeUnitaryFlow
-- name    : BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T11:52:28.075775+00:00
-- url     : https://prove2.me/theorems/68e223e1-7786-4856-a692-0db7e00a316b
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow` (U : ℝ → F → F) (hnorm : ∀ (t : ℝ) (v : F), ‖U t v‖ = ‖v‖) (hU0 : ∀ v : F, U 0 v = v) (hU
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow` (U : ℝ → F → F) (hnorm : ∀ (t : ℝ) (v : F), ‖U t v‖ = ‖v‖) (hU0 : ∀ v : F, U 0 v = v) (hUD : ∀ (t : ℝ) (v : d.D), U t (v : F) ∈ d.D) (hderiv : ∀ (v : d.D) (t : ℝ), HasDerivAt (fun s => U s (v : F)) (Complex.I • (d.hamiltonian ⟨U t (v : F), hUD t v⟩ : F)) t) : HasZeroDeficiencyOn d.D d.hamiltonian
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow (U : ℝ → F → F)
    (hnorm : ∀ (t : ℝ) (v : F), ‖U t v‖ = ‖v‖) (hU0 : ∀ v : F, U 0 v = v)
    (hUD : ∀ (t : ℝ) (v : d.D), U t (v : F) ∈ d.D)
    (hderiv : ∀ (v : d.D) (t : ℝ),
      HasDerivAt (fun s => U s (v : F))
        (Complex.I • (d.hamiltonian ⟨U t (v : F), hUD t v⟩ : F)) t) :
    HasZeroDeficiencyOn d.D d.hamiltonian := by sorry
