-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_dens_eq_one_of_invariant
-- name    : BookProof.ChapterMackeyQuasiInvariant.dens_eq_one_of_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:53:35.679132+00:00
-- url     : https://prove2.me/theorems/868e9b08-72d8-4556-a7ee-0f32db61811a
-- title:
--   `BookProof.ChapterMackeyQuasiInvariant.dens_eq_one_of_invariant` {μ : Measure X} [SigmaFinite μ] (hinv : ∀ g : G, (μ.map fun x : X => g • x) = μ) (g : G) : dens μ g =ᵐ[μ] fun _ =>
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyQuasiInvariant`.
--
--   `BookProof.ChapterMackeyQuasiInvariant.dens_eq_one_of_invariant` {μ : Measure X} [SigmaFinite μ] (hinv : ∀ g : G, (μ.map fun x : X => g • x) = μ) (g : G) : dens μ g =ᵐ[μ] fun _ => 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyQuasiInvariant.dens_eq_one_of_invariant`.

-- Generated from ChapterMackeyQuasiInvariant.lean — theorem BookProof.ChapterMackeyQuasiInvariant.dens_eq_one_of_invariant
import Mathlib
import Definitions.Def_ChapterMackeyQuasiInvariant
open BookProof.ChapterMackeyQuasiInvariant


open MeasureTheory Measure


variable {G X K : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable (μ : Measure X) (L : G → X → (K ≃ₗᵢ[ℂ] K))
variable {μ L}

theorem BookProof.ChapterMackeyQuasiInvariant.dens_eq_one_of_invariant {μ : Measure X} [SigmaFinite μ]
    (hinv : ∀ g : G, (μ.map fun x : X => g • x) = μ) (g : G) :
    dens μ g =ᵐ[μ] fun _ => 1 := by sorry
