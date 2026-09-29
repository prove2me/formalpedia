-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_ym_hermite_hashimoto_selects
-- name    : BookProof.YangMillsHermite.ym_hermite_hashimoto_selects
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:51:48.486398+00:00
-- url     : https://prove2.me/theorems/c545fccc-4e5d-4300-841f-7c8450d9d46e
-- title:
--   (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {γ : ℝ} (hγ : 0 < γ) : ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99) (R : L2d 99 →L[ℂ] L2d 99), IsPositiveSelfAdjointExtension (ym...
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.ym_hermite_hashimoto_selects` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.ym_hermite_hashimoto_selects
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

















































variable {D : Submodule ℂ (L2d d)}












variable {D : Submodule ℂ (L2d 99)}

theorem BookProof.YangMillsHermite.ym_hermite_hashimoto_selects (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99) (R : L2d 99 →L[ℂ] L2d 99),
      IsPositiveSelfAdjointExtension (ymHamiltonian (coreRepBasis e) fabc) A ∧
        IsShiftInvert A γ R ∧ IsSelfAdjoint R ∧
        (∀ u : L2d 99, Filter.Tendsto (fun k : ℕ => galerkinCompression R (coreBasis e) k u)
          Filter.atTop (nhds (R u))) ∧
        (∀ (Dom' : Submodule ℂ (L2d 99)) (A' : Dom' →ₗ[ℂ] L2d 99),
          IsShiftInvert A' γ R → Dom' = Dom) := by sorry
