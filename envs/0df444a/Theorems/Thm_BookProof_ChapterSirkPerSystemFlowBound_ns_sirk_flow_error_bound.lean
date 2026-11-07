-- Prove2me | Theorems.Thm_BookProof_ChapterSirkPerSystemFlowBound_ns_sirk_flow_error_bound
-- name    : BookProof.ChapterSirkPerSystemFlowBound.ns_sirk_flow_error_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T19:43:13.284201+00:00
-- url     : https://prove2.me/theorems/3d2f4b69-5886-4fee-a944-61f3a2a7744a
-- title:
--   `BookProof.ChapterSirkPerSystemFlowBound.ns_sirk_flow_error_bound` (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (b : HilbertBasis ℕ ℂ (L2I Vel)) (γ : ℕ → ℂ) (hγ : ∀ j, (γ...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkPerSystemFlowBound`.
--
--   `BookProof.ChapterSirkPerSystemFlowBound.ns_sirk_flow_error_bound` (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (b : HilbertBasis ℕ ℂ (L2I Vel)) (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) : ∃ (Dom : Submodule ℂ (L2I Vel)) (G : Dom →ₗ[ℂ] L2I Vel) (X : ℕ → L2I Vel →L[ℂ] L2I Vel), IsSelfAdjointExtension (velCore A c) G ∧ (∀ j, IsShiftInvertC G (γ j) (X j)) ∧ (∀ j, numRange (X j) ⊆ Metric.closedBall (0 : ℂ) |(γ j).im|⁻¹) ∧ ∀ (j m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2I Vel) (s : RationalScheme (L2I Vel) (EuclideanSpace ℂ (Fin m))) (C Dmin h : ℝ), IsSirkScheme (X j) V (Metric.closedBall (0 : ℂ) |(γ j).im|⁻¹) C Dmin h m s → ∀ (flow : L2I Vel →L[ℂ] L2I Vel), flow = s.psiX → ∀ v : L2I Vel, V (V.adjoint v) = v → ‖flow v - sirkApprox V s.psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSirkPerSystemFlowBound.ns_sirk_flow_error_bound`.

-- Generated from ChapterSirkPerSystemFlowBound.lean — theorem BookProof.ChapterSirkPerSystemFlowBound.ns_sirk_flow_error_bound
import Definitions.Def_ChapterSirkSpectralGeometry
import Definitions.Def_ChapterSirkPerSystem
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesDiffHashimoto
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Mathlib
import Definitions.Def_ChapterSirkPerSystemFlowBound
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH9
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHashimoto
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterSirkEndToEnd
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSirkPerSystemFlowBound
open BookProof.EsaClosure
open BookProof.ChapterH4
open BookProof.ChapterH6
open BookProof.ChapterH9
open BookProof.HashimotoShiftInvert
open BookProof.NavierStokesFlow.NSHashimoto
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.ThreeComponent
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

theorem BookProof.ChapterSirkPerSystemFlowBound.ns_sirk_flow_error_bound (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
    (b : HilbertBasis ℕ ℂ (L2I Vel)) (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ (L2I Vel)) (G : Dom →ₗ[ℂ] L2I Vel)
      (X : ℕ → L2I Vel →L[ℂ] L2I Vel),
      IsSelfAdjointExtension (velCore A c) G ∧
      (∀ j, IsShiftInvertC G (γ j) (X j)) ∧
      (∀ j, numRange (X j) ⊆ Metric.closedBall (0 : ℂ) |(γ j).im|⁻¹) ∧
      ∀ (j m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2I Vel)
        (s : RationalScheme (L2I Vel) (EuclideanSpace ℂ (Fin m))) (C Dmin h : ℝ),
        IsSirkScheme (X j) V (Metric.closedBall (0 : ℂ) |(γ j).im|⁻¹) C Dmin h m s →
        ∀ (flow : L2I Vel →L[ℂ] L2I Vel), flow = s.psiX →
        ∀ v : L2I Vel, V (V.adjoint v) = v →
          ‖flow v - sirkApprox V s.psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by sorry
