-- Prove2me | Theorems.Thm_BookProof_ChapterSirkPerSystemFlowBound_diagKR_sirk_flow_error_bound
-- name    : BookProof.ChapterSirkPerSystemFlowBound.diagKR_sirk_flow_error_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-02T09:32:13.230285+00:00
-- url     : https://prove2.me/theorems/2a7fd140-ea64-4d41-977a-a25702370e40
-- title:
--   `BookProof.ChapterSirkPerSystemFlowBound.diagKR_sirk_flow_error_bound` (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) : ∃ (Dom : Submodule ℂ L2N) (A : Dom →ₗ[ℂ] L2N) (X : ℕ →...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkPerSystemFlowBound`.
--
--   `BookProof.ChapterSirkPerSystemFlowBound.diagKR_sirk_flow_error_bound` (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) : ∃ (Dom : Submodule ℂ L2N) (A : Dom →ₗ[ℂ] L2N) (X : ℕ → L2N →L[ℂ] L2N), IsSelfAdjointExtension (lagrangianCore diagKR) A ∧ (∀ j, IsShiftInvertC A (γ j) (X j)) ∧ (∀ j, numRange (X j) ⊆ Metric.closedBall (0 : ℂ) |(γ j).im|⁻¹) ∧ ∀ (j m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2N) (s : RationalScheme L2N (EuclideanSpace ℂ (Fin m))) (C Dmin h : ℝ), IsSirkScheme (X j) V (Metric.closedBall (0 : ℂ) |(γ j).im|⁻¹) C Dmin h m s → ∀ (flow : L2N →L[ℂ] L2N), flow = s.psiX → ∀ v : L2N, V (V.adjoint v) = v → ‖flow v - sirkApprox V s.psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSirkPerSystemFlowBound.diagKR_sirk_flow_error_bound`.

-- Generated from ChapterSirkPerSystemFlowBound.lean — theorem BookProof.ChapterSirkPerSystemFlowBound.diagKR_sirk_flow_error_bound
import Definitions.Def_ChapterSirkSpectralGeometry
import Definitions.Def_ChapterSirkPerSystem
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesHashimoto
import Definitions.Def_ChapterNavierStokesDiffHashimoto
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Mathlib
import Definitions.Def_ChapterSirkPerSystemFlowBound
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH9
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterSirkEndToEnd
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSirkPerSystemFlowBound
open BookProof.EsaClosure
open BookProof.ChapterH4
open BookProof.ChapterH6
open BookProof.ChapterH9
open BookProof.HashimotoShiftInvert
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.ChapterSirkEndToEnd
open BookProof.ChapterSirkPerSystemFlowBound


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

variable {E G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkPerSystemFlowBound.diagKR_sirk_flow_error_bound (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ L2N) (A : Dom →ₗ[ℂ] L2N) (X : ℕ → L2N →L[ℂ] L2N),
      IsSelfAdjointExtension (lagrangianCore diagKR) A ∧
      (∀ j, IsShiftInvertC A (γ j) (X j)) ∧
      (∀ j, numRange (X j) ⊆ Metric.closedBall (0 : ℂ) |(γ j).im|⁻¹) ∧
      ∀ (j m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2N)
        (s : RationalScheme L2N (EuclideanSpace ℂ (Fin m))) (C Dmin h : ℝ),
        IsSirkScheme (X j) V (Metric.closedBall (0 : ℂ) |(γ j).im|⁻¹) C Dmin h m s →
        ∀ (flow : L2N →L[ℂ] L2N), flow = s.psiX →
        ∀ v : L2N, V (V.adjoint v) = v →
          ‖flow v - sirkApprox V s.psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by sorry
