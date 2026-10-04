-- Prove2me | Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_hashimoto_selects
-- name    : BookProof.FriedrichsExtension.friedrichs_hashimoto_selects
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-03T07:54:11.045994+00:00
-- url     : https://prove2.me/theorems/b63c674b-b86a-4bc9-898e-fb6567aac2b0
-- title:
--   The Lean 4 theorem `friedrichs_hashimoto_selects` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `friedrichs_hashimoto_selects` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsExtension.lean

-- Generated from ChapterFriedrichsExtension.lean — theorem BookProof.FriedrichsExtension.friedrichs_hashimoto_selects
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open scoped InnerProductSpace ENNReal lp


open Filter Topology

theorem BookProof.FriedrichsExtension.friedrichs_hashimoto_selects (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn (finiteModeDomain b) H)
    (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (R : F →L[ℂ] F),
      IsPositiveSelfAdjointExtension H A ∧ IsShiftInvert A γ R ∧ ‖R‖ ≤ γ⁻¹ ∧
        IsSelfAdjoint R ∧
        (∀ u : F, Tendsto (fun k : ℕ => galerkinCompression R b k u) atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : F,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R b k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvert A' γ R →
          Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by sorry
