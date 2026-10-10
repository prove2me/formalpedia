-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_mackey_inducedSystem_continuous
-- name    : BookProof.ChapterMackeyQuasiInvariant.mackey_inducedSystem_continuous
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:53:27.144152+00:00
-- url     : https://prove2.me/theorems/2734fd4d-8263-4f1a-abe0-a2327e9449e7
-- title:
--   `BookProof.ChapterMackeyQuasiInvariant.mackey_inducedSystem_continuous` [SigmaFinite μ] (h : QuasiInvariant μ G) (hL : UnitaryCocycle μ L) : (∀ (g : G) (f₁ f₂ : Lp K 2 μ), vmap h h
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyQuasiInvariant`.
--
--   `BookProof.ChapterMackeyQuasiInvariant.mackey_inducedSystem_continuous` [SigmaFinite μ] (h : QuasiInvariant μ G) (hL : UnitaryCocycle μ L) : (∀ (g : G) (f₁ f₂ : Lp K 2 μ), vmap h hL g (f₁ + f₂) = vmap h hL g f₁ + vmap h hL g f₂) ∧ (∀ (g : G) (c : ℂ) (f : Lp K 2 μ), vmap h hL g (c • f) = c • vmap h hL g f) ∧ (∀ (g : G) (f : Lp K 2 μ), ‖vmap h hL g f‖ = ‖f‖) ∧ (∀ f : Lp K 2 μ, vmap h hL (1 : G) f = f) ∧ (∀ (g k : G) (f : Lp K 2 μ), vmap h hL g (vmap h hL k f) = vmap h hL (g * k) f) ∧ (∀ (E : Set X) (hE : MeasurableSet E) (f : Lp K 2 μ), proj μ hE (proj μ hE f) = proj μ hE f) ∧ (∀ f : Lp K 2 μ, proj μ MeasurableSet.univ f = f) ∧ (∀ (E : Set X) (hE : MeasurableSet E) (f f' : Lp K 2 μ), (inner ℂ (proj μ hE f) f' : ℂ) = inner ℂ f (proj μ hE f')) ∧ (∀ (g : G) (E : Set X) (hE : MeasurableSet E) (f : Lp K 2 μ), vmap h hL g (proj μ hE (vmap h hL g⁻¹ f)) = proj μ ((actEquiv h.measurable g).measurableSet_image.mpr hE) f)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyQuasiInvariant.mackey_inducedSystem_continuous`.

-- Generated from ChapterMackeyQuasiInvariant.lean — theorem BookProof.ChapterMackeyQuasiInvariant.mackey_inducedSystem_continuous
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

theorem BookProof.ChapterMackeyQuasiInvariant.mackey_inducedSystem_continuous [SigmaFinite μ] (h : QuasiInvariant μ G)
    (hL : UnitaryCocycle μ L) :
    (∀ (g : G) (f₁ f₂ : Lp K 2 μ),
        vmap h hL g (f₁ + f₂) = vmap h hL g f₁ + vmap h hL g f₂) ∧
    (∀ (g : G) (c : ℂ) (f : Lp K 2 μ), vmap h hL g (c • f) = c • vmap h hL g f) ∧
    (∀ (g : G) (f : Lp K 2 μ), ‖vmap h hL g f‖ = ‖f‖) ∧
    (∀ f : Lp K 2 μ, vmap h hL (1 : G) f = f) ∧
    (∀ (g k : G) (f : Lp K 2 μ), vmap h hL g (vmap h hL k f) = vmap h hL (g * k) f) ∧
    (∀ (E : Set X) (hE : MeasurableSet E) (f : Lp K 2 μ),
        proj μ hE (proj μ hE f) = proj μ hE f) ∧
    (∀ f : Lp K 2 μ, proj μ MeasurableSet.univ f = f) ∧
    (∀ (E : Set X) (hE : MeasurableSet E) (f f' : Lp K 2 μ),
        (inner ℂ (proj μ hE f) f' : ℂ) = inner ℂ f (proj μ hE f')) ∧
    (∀ (g : G) (E : Set X) (hE : MeasurableSet E) (f : Lp K 2 μ),
        vmap h hL g (proj μ hE (vmap h hL g⁻¹ f))
          = proj μ ((actEquiv h.measurable g).measurableSet_image.mpr hE) f) := by sorry
