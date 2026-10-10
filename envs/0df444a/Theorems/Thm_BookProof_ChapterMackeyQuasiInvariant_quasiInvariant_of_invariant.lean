-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_quasiInvariant_of_invariant
-- name    : BookProof.ChapterMackeyQuasiInvariant.quasiInvariant_of_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:53:22.519979+00:00
-- url     : https://prove2.me/theorems/c3dbf749-6f19-4abe-a2e7-afdceaf8dbb5
-- title:
--   `BookProof.ChapterMackeyQuasiInvariant.quasiInvariant_of_invariant` {μ : Measure X} (hm : ∀ g : G, Measurable fun x : X => g • x) (hinv : ∀ g : G, (μ.map fun x : X => g • x) = μ) :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyQuasiInvariant`.
--
--   `BookProof.ChapterMackeyQuasiInvariant.quasiInvariant_of_invariant` {μ : Measure X} (hm : ∀ g : G, Measurable fun x : X => g • x) (hinv : ∀ g : G, (μ.map fun x : X => g • x) = μ) : QuasiInvariant μ G
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyQuasiInvariant.quasiInvariant_of_invariant`.

-- Generated from ChapterMackeyQuasiInvariant.lean — theorem BookProof.ChapterMackeyQuasiInvariant.quasiInvariant_of_invariant
import Mathlib
import Definitions.Def_ChapterMackeyQuasiInvariant
open BookProof.ChapterMackeyQuasiInvariant


open MeasureTheory Measure


variable {G X K : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable (μ : Measure X) (L : G → X → (K ≃ₗᵢ[ℂ] K))
variable {μ L}

theorem BookProof.ChapterMackeyQuasiInvariant.quasiInvariant_of_invariant {μ : Measure X}
    (hm : ∀ g : G, Measurable fun x : X => g • x)
    (hinv : ∀ g : G, (μ.map fun x : X => g • x) = μ) : QuasiInvariant μ G := by sorry
