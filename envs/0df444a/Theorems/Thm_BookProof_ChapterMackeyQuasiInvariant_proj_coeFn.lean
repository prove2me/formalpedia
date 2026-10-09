-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_proj_coeFn
-- name    : BookProof.ChapterMackeyQuasiInvariant.proj_coeFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T09:32:47.265726+00:00
-- url     : https://prove2.me/theorems/5f304f31-cb7e-42b4-a988-a59129321fe2
-- title:
--   `BookProof.ChapterMackeyQuasiInvariant.proj_coeFn` (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f : Lp K 2 μ) : (proj μ hE f : X → K) =ᵐ[μ] E.indicator (f : X → K)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyQuasiInvariant`.
--
--   `BookProof.ChapterMackeyQuasiInvariant.proj_coeFn` (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f : Lp K 2 μ) : (proj μ hE f : X → K) =ᵐ[μ] E.indicator (f : X → K)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyQuasiInvariant.proj_coeFn`.

-- Generated from ChapterMackeyQuasiInvariant.lean — theorem BookProof.ChapterMackeyQuasiInvariant.proj_coeFn
import Mathlib
import Definitions.Def_ChapterMackeyQuasiInvariant
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterMackeyQuasiInvariant


open MeasureTheory Measure


variable {G X K : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable (μ : Measure X) (L : G → X → (K ≃ₗᵢ[ℂ] K))
variable {μ L}

theorem BookProof.ChapterMackeyQuasiInvariant.proj_coeFn (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f : Lp K 2 μ) :
    (proj μ hE f : X → K) =ᵐ[μ] E.indicator (f : X → K) := by sorry
