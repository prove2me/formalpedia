-- Prove2me | Theorems.Thm_BookProof_ChapterSirkPerSystemFlowBound_ym_sirk_flow_error_bound
-- name    : BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:51:23.748629+00:00
-- url     : https://prove2.me/theorems/6a90927c-282a-45e8-bbc8-3abb7adfbbd0
-- title:
--   `BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_bound` (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {γ : ℝ} (hγ : 0 < γ) : ∃ (Dom : Submodule...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkPerSystemFlowBound`.
--
--   `BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_bound` (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {γ : ℝ} (hγ : 0 < γ) : ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99) (R : L2d 99 →L[ℂ] L2d 99), IsPositiveSelfAdjointExtension (ymHamiltonian (coreRepBasis e) fabc) A ∧ IsShiftInvert A γ R ∧ IsSelfAdjoint R ∧ numRange R ⊆ realSegment 0 γ⁻¹ ∧ ∀ (m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2d 99) (s : RationalScheme (L2d 99) (EuclideanSpace ℂ (Fin m))) (C Dmin h : ℝ), IsSirkScheme R V (realSegment 0 γ⁻¹) C Dmin h m s → ∀ (flow : L2d 99 →L[ℂ] L2d 99), flow = s.psiX → ∀ v : L2d 99, V (V.adjoint v) = v → ‖flow v - sirkApprox V s.psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_bound`.

-- Generated from ChapterSirkPerSystemFlowBound.lean — theorem BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_bound
import Definitions.Def_ChapterSirkPerSystem
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesHashimoto
import Definitions.Def_ChapterNavierStokesDiffHashimoto
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Mathlib
import Definitions.Def_ChapterSirkPerSystemFlowBound
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH9
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSirkEndToEnd
import Definitions.Def_ChapterSirkSpectralGeometry
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
open BookProof.ChapterH4
open BookProof.ChapterH6
open BookProof.ChapterH9
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
open BookProof.ChapterSirkEndToEnd
open BookProof.ChapterSirkSpectralGeometry
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsHermite
open BookProof.ChapterSirkPerSystemFlowBound

variable {E G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]


noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.ChapterSirkSpectralGeometry
open BookProof.ChapterSirkPerSystem
open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.EsaClosure
open BookProof.YangMillsFriedrichs BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.Starobinsky
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.NSHashimoto
open BookProof.NavierStokesFlow.DiffHashimoto BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow.LagrangianEsa BookProof.NavierStokesFlow.LagrangianKatoRellich

theorem BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_bound (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99) (R : L2d 99 →L[ℂ] L2d 99),
      IsPositiveSelfAdjointExtension (ymHamiltonian (coreRepBasis e) fabc) A ∧
        IsShiftInvert A γ R ∧ IsSelfAdjoint R ∧
        numRange R ⊆ realSegment 0 γ⁻¹ ∧
        ∀ (m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2d 99)
          (s : RationalScheme (L2d 99) (EuclideanSpace ℂ (Fin m))) (C Dmin h : ℝ),
          IsSirkScheme R V (realSegment 0 γ⁻¹) C Dmin h m s →
          ∀ (flow : L2d 99 →L[ℂ] L2d 99), flow = s.psiX →
          ∀ v : L2d 99, V (V.adjoint v) = v →
            ‖flow v - sirkApprox V s.psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by sorry
