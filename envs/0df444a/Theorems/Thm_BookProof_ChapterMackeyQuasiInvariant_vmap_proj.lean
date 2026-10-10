-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_vmap_proj
-- name    : BookProof.ChapterMackeyQuasiInvariant.vmap_proj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:53:06.785826+00:00
-- url     : https://prove2.me/theorems/8382b898-16f0-4758-825f-cd3c48d7cc44
-- title:
--   `BookProof.ChapterMackeyQuasiInvariant.vmap_proj` [SigmaFinite μ] (h : QuasiInvariant μ G) (hL : UnitaryCocycle μ L) (g : G) {E : Set X} (hE : MeasurableSet E) (f : Lp K 2 μ) : vma
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyQuasiInvariant`.
--
--   `BookProof.ChapterMackeyQuasiInvariant.vmap_proj` [SigmaFinite μ] (h : QuasiInvariant μ G) (hL : UnitaryCocycle μ L) (g : G) {E : Set X} (hE : MeasurableSet E) (f : Lp K 2 μ) : vmap h hL g (proj μ hE f) = proj μ ((actEquiv h.measurable g).measurableSet_image.mpr hE) (vmap h hL g f)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyQuasiInvariant.vmap_proj`.

-- Generated from ChapterMackeyQuasiInvariant.lean — theorem BookProof.ChapterMackeyQuasiInvariant.vmap_proj
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

theorem BookProof.ChapterMackeyQuasiInvariant.vmap_proj [SigmaFinite μ] (h : QuasiInvariant μ G) (hL : UnitaryCocycle μ L)
    (g : G) {E : Set X} (hE : MeasurableSet E) (f : Lp K 2 μ) :
    vmap h hL g (proj μ hE f)
      = proj μ ((actEquiv h.measurable g).measurableSet_image.mpr hE)
          (vmap h hL g f) := by sorry
