-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_hashimoto_shiftInvert_selects_friedrichs
-- name    : BookProof.HashimotoShiftInvert.hashimoto_shiftInvert_selects_friedrichs
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-02T10:02:40.510039+00:00
-- url     : https://prove2.me/theorems/2e4f603a-eed4-493b-8e68-c0189f1e5aa6
-- title:
--   The Lean 4 theorem `hashimoto_shiftInvert_selects_friedrichs` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hashimoto_shiftInvert_selects_friedrichs` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.hashimoto_shiftInvert_selects_friedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem BookProof.HashimotoShiftInvert.hashimoto_shiftInvert_selects_friedrichs (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] F)
    (hA : IsPositiveSelfAdjointExtension H A) {γ : ℝ} (hγ : 0 < γ) :
    ∃ R : F →L[ℂ] F,
      IsShiftInvert A γ R ∧ ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
      (∀ u : F, 0 ≤ (inner ℂ u (R u) : ℂ).re) ∧
      (∀ u : F, Tendsto (fun m : ℕ => galerkinCompression R b m u) atTop (nhds (R u))) ∧
      (∀ z : ℂ, z.im ≠ 0 → ∀ u : F,
        Tendsto (fun m : ℕ => resolvent (galerkinCompression R b m) z u) atTop
          (nhds (resolvent R z u))) ∧
      (∀ (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvert A' γ R →
        Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by sorry
