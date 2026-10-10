-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_proj_add_of_disjoint
-- name    : BookProof.ChapterMackeyQuasiInvariant.proj_add_of_disjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:53:00.625847+00:00
-- url     : https://prove2.me/theorems/ef84d488-3948-4064-a853-1d3fac48aa0a
-- title:
--   `BookProof.ChapterMackeyQuasiInvariant.proj_add_of_disjoint` (μ : Measure X) {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F) (hd : Disjoint E F) (f : Lp K 2 μ) : proj μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyQuasiInvariant`.
--
--   `BookProof.ChapterMackeyQuasiInvariant.proj_add_of_disjoint` (μ : Measure X) {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F) (hd : Disjoint E F) (f : Lp K 2 μ) : proj μ (hE.union hF) f = proj μ hE f + proj μ hF f
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyQuasiInvariant.proj_add_of_disjoint`.

-- Generated from ChapterMackeyQuasiInvariant.lean — theorem BookProof.ChapterMackeyQuasiInvariant.proj_add_of_disjoint
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

theorem BookProof.ChapterMackeyQuasiInvariant.proj_add_of_disjoint (μ : Measure X) {E F : Set X} (hE : MeasurableSet E)
    (hF : MeasurableSet F) (hd : Disjoint E F) (f : Lp K 2 μ) :
    proj μ (hE.union hF) f = proj μ hE f + proj μ hF f := by sorry
