-- Prove2me | Theorems.Thm_BookProof_QuantumGravityFock_qgFock_hashimoto_selects
-- name    : BookProof.QuantumGravityFock.qgFock_hashimoto_selects
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:46:48.733233+00:00
-- url     : https://prove2.me/theorems/4de83d80-75e4-42fc-b434-cfc7d861ecb2
-- title:
--   `BookProof.QuantumGravityFock.qgFock_hashimoto_selects` (e84 : ℕ ≃ (Fin 84 →₀ ℕ)) (eps : ℕ ≃ BoseConf) (A : finiteModeDomain (BookProof.HermiteProductCore.coreBasis e84) →ₗ[ℂ] fini
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityFock`.
--
--   `BookProof.QuantumGravityFock.qgFock_hashimoto_selects` (e84 : ℕ ≃ (Fin 84 →₀ ℕ)) (eps : ℕ ≃ BoseConf) (A : finiteModeDomain (BookProof.HermiteProductCore.coreBasis e84) →ₗ[ℂ] finiteModeDomain (BookProof.HermiteProductCore.coreBasis e84)) (hA : SymmetricOn (finiteModeDomain (BookProof.HermiteProductCore.coreBasis e84)) ((finiteModeDomain (BookProof.HermiteProductCore.coreBasis e84)).subtype.comp A)) (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain (BookProof.HermiteProductCore.coreBasis e84)).subtype.comp A) x) {gamma : ℝ} (hgamma : 0 < gamma) : ∃ (Dom : Submodule ℂ BookProof.FockSecondQuantization.Fock) (A' : Dom →ₗ[ℂ] BookProof.FockSecondQuantization.Fock) (R : BookProof.FockSecondQuantization.Fock →L[ℂ] BookProof.FockSecondQuantization.Fock), IsPositiveSelfAdjointExtension (dGammaOpB eps (opCol (BookProof.HermiteProductCore.coreBasis e84) A)) A' ∧ IsShiftInvert A' gamma R ∧ ‖R‖ ≤ gamma⁻¹ ∧ IsSelfAdjoint R ∧ (∀ u : BookProof.FockSecondQuantization.Fock, Filter.Tendsto (fun k : ℕ => galerkinCompression R (fockBasisN eps) k u) Filter.atTop (nhds (R u))) ∧ (∀ z : ℂ, z.im ≠ 0 → ∀ u : BookProof.FockSecondQuantization.Fock, Filter.Tendsto (fun k : ℕ => resolvent (galerkinCompression R (fockBasisN eps) k) z u) Filter.atTop (nhds (resolvent R z u))) ∧ (∀ (Dom' : Submodule ℂ BookProof.FockSecondQuantization.Fock) (A'' : Dom' →ₗ[ℂ] BookProof.FockSecondQuantization.Fock), IsShiftInvert A'' gamma R → Dom' = Dom ∧ ∀ (x : BookProof.FockSecondQuantization.Fock) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A'' ⟨x, hx'⟩ = A' ⟨x, hx⟩)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityFock.qgFock_hashimoto_selects`.

-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgFock_hashimoto_selects
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterQuantumGravityFock
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section

theorem BookProof.QuantumGravityFock.qgFock_hashimoto_selects (e84 : ℕ ≃ (Fin 84 →₀ ℕ)) (eps : ℕ ≃ BoseConf)
    (A : finiteModeDomain (BookProof.HermiteProductCore.coreBasis e84) →ₗ[ℂ]
      finiteModeDomain (BookProof.HermiteProductCore.coreBasis e84))
    (hA : SymmetricOn (finiteModeDomain (BookProof.HermiteProductCore.coreBasis e84))
      ((finiteModeDomain (BookProof.HermiteProductCore.coreBasis e84)).subtype.comp A))
    (hpos : ∀ x, 0 ≤ quadForm
      ((finiteModeDomain (BookProof.HermiteProductCore.coreBasis e84)).subtype.comp A) x)
    {gamma : ℝ} (hgamma : 0 < gamma) :
    ∃ (Dom : Submodule ℂ BookProof.FockSecondQuantization.Fock)
      (A' : Dom →ₗ[ℂ] BookProof.FockSecondQuantization.Fock)
      (R : BookProof.FockSecondQuantization.Fock →L[ℂ] BookProof.FockSecondQuantization.Fock),
      IsPositiveSelfAdjointExtension
        (dGammaOpB eps (opCol (BookProof.HermiteProductCore.coreBasis e84) A)) A' ∧
        IsShiftInvert A' gamma R ∧ ‖R‖ ≤ gamma⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : BookProof.FockSecondQuantization.Fock,
          Filter.Tendsto (fun k : ℕ => galerkinCompression R (fockBasisN eps) k u)
            Filter.atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : BookProof.FockSecondQuantization.Fock,
          Filter.Tendsto (fun k : ℕ => resolvent (galerkinCompression R (fockBasisN eps) k) z u)
            Filter.atTop (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ BookProof.FockSecondQuantization.Fock)
          (A'' : Dom' →ₗ[ℂ] BookProof.FockSecondQuantization.Fock),
          IsShiftInvert A'' gamma R →
            Dom' = Dom ∧ ∀ (x : BookProof.FockSecondQuantization.Fock) (hx : x ∈ Dom)
              (hx' : x ∈ Dom'), A'' ⟨x, hx'⟩ = A' ⟨x, hx⟩) := by sorry
