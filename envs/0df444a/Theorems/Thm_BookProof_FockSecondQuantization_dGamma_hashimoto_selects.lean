-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dGamma_hashimoto_selects
-- name    : BookProof.FockSecondQuantization.dGamma_hashimoto_selects
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:28:59.156411+00:00
-- url     : https://prove2.me/theorems/ca49ccf6-abce-4287-be98-0f119dc9fd01
-- title:
--   (ε : ℕ ≃ Conf) {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) (hpos : IsPosCol col) {γ : ℝ} (hγ : 0 < γ) : ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock) (R :...
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dGamma_hashimoto_selects` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dGamma_hashimoto_selects
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open Filter Topology

theorem BookProof.FockSecondQuantization.dGamma_hashimoto_selects (ε : ℕ ≃ Conf) {col : ℕ → (ℕ →₀ ℂ)}
    (hherm : IsHermCol col) (hpos : IsPosCol col) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock) (R : Fock →L[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOpB ε col) A ∧ IsShiftInvert A γ R ∧
        ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : Fock, Tendsto (fun k : ℕ => galerkinCompression R (fockBasisN ε) k u)
          atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : Fock,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R (fockBasisN ε) k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ Fock) (A' : Dom' →ₗ[ℂ] Fock), IsShiftInvert A' γ R →
          Dom' = Dom ∧ ∀ (x : Fock) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by sorry
