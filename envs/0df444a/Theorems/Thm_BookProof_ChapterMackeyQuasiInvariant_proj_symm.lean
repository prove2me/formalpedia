-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_proj_symm
-- name    : BookProof.ChapterMackeyQuasiInvariant.proj_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:52:56.449395+00:00
-- url     : https://prove2.me/theorems/47a9f6e9-72e5-4624-b5e0-077fbdbc9819
-- title:
--   `BookProof.ChapterMackeyQuasiInvariant.proj_symm` (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f f' : Lp K 2 μ) : (inner ℂ (proj μ hE f) f' : ℂ) = inner ℂ f (proj μ hE f')
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyQuasiInvariant`.
--
--   `BookProof.ChapterMackeyQuasiInvariant.proj_symm` (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f f' : Lp K 2 μ) : (inner ℂ (proj μ hE f) f' : ℂ) = inner ℂ f (proj μ hE f')
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyQuasiInvariant.proj_symm`.

-- Generated from ChapterMackeyQuasiInvariant.lean — theorem BookProof.ChapterMackeyQuasiInvariant.proj_symm
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

theorem BookProof.ChapterMackeyQuasiInvariant.proj_symm (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f f' : Lp K 2 μ) :
    (inner ℂ (proj μ hE f) f' : ℂ) = inner ℂ f (proj μ hE f') := by sorry
