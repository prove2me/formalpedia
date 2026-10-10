-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_proj_inter
-- name    : BookProof.ChapterMackeyQuasiInvariant.proj_inter
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:52:17.525535+00:00
-- url     : https://prove2.me/theorems/b2f0b23d-607f-453a-ab4b-a42c83940e04
-- title:
--   `BookProof.ChapterMackeyQuasiInvariant.proj_inter` (μ : Measure X) {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F) (f : Lp K 2 μ) : proj μ hE (proj μ hF f) = proj μ (hE
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyQuasiInvariant`.
--
--   `BookProof.ChapterMackeyQuasiInvariant.proj_inter` (μ : Measure X) {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F) (f : Lp K 2 μ) : proj μ hE (proj μ hF f) = proj μ (hE.inter hF) f
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyQuasiInvariant.proj_inter`.

-- Generated from ChapterMackeyQuasiInvariant.lean — theorem BookProof.ChapterMackeyQuasiInvariant.proj_inter
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

theorem BookProof.ChapterMackeyQuasiInvariant.proj_inter (μ : Measure X) {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (f : Lp K 2 μ) : proj μ hE (proj μ hF f) = proj μ (hE.inter hF) f := by sorry
