-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_proj_idem
-- name    : BookProof.ChapterMackeyQuasiInvariant.proj_idem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:52:11.367665+00:00
-- url     : https://prove2.me/theorems/d85ac871-5441-4173-bc60-b0ae025592c7
-- title:
--   `BookProof.ChapterMackeyQuasiInvariant.proj_idem` (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f : Lp K 2 μ) : proj μ hE (proj μ hE f) = proj μ hE f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyQuasiInvariant`.
--
--   `BookProof.ChapterMackeyQuasiInvariant.proj_idem` (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f : Lp K 2 μ) : proj μ hE (proj μ hE f) = proj μ hE f
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyQuasiInvariant.proj_idem`.

-- Generated from ChapterMackeyQuasiInvariant.lean — theorem BookProof.ChapterMackeyQuasiInvariant.proj_idem
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

theorem BookProof.ChapterMackeyQuasiInvariant.proj_idem (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f : Lp K 2 μ) :
    proj μ hE (proj μ hE f) = proj μ hE f := by sorry
