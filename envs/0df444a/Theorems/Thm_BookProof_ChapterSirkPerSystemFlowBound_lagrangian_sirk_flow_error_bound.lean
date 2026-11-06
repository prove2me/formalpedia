-- Prove2me | Theorems.Thm_BookProof_ChapterSirkPerSystemFlowBound_lagrangian_sirk_flow_error_bound
-- name    : BookProof.ChapterSirkPerSystemFlowBound.lagrangian_sirk_flow_error_bound
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-05T19:43:28.931655+00:00
-- url     : https://prove2.me/theorems/1d6d9024-0758-4389-a523-7609b7b72e54
-- title:
--   `BookProof.ChapterSirkPerSystemFlowBound.lagrangian_sirk_flow_error_bound` {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (L : LagrangianFullData F) (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkPerSystemFlowBound`.
--
--   `BookProof.ChapterSirkPerSystemFlowBound.lagrangian_sirk_flow_error_bound` {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (L : LagrangianFullData F) (hesa : EssentiallySelfAdjointOn L.D (lagrangianCore L)) {γ : ℂ} (hγ : γ.im ≠ 0) : ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (X : F →L[ℂ] F), IsSelfAdjointExtension (lagrangianCore L) A ∧ IsShiftInvertC A γ X ∧ ‖X‖ ≤ |γ.im|⁻¹ ∧ numRange X ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ ∧ ∀ (m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] F) (s : RationalScheme F (EuclideanSpace ℂ (Fin m))) (C Dmin h : ℝ), IsSirkScheme X V (Metric.closedBall (0 : ℂ) |γ.im|⁻¹) C Dmin h m s → ∀ (flow : F →L[ℂ] F), flow = s.psiX → ∀ v : F, V (V.adjoint v) = v → ‖flow v - sirkApprox V s.psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSirkPerSystemFlowBound.lagrangian_sirk_flow_error_bound`.

-- Generated from ChapterSirkPerSystemFlowBound.lean — theorem BookProof.ChapterSirkPerSystemFlowBound.lagrangian_sirk_flow_error_bound
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
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesHashimoto
import Definitions.Def_ChapterNavierStokesDiffHashimoto
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterSirkPerSystemFlowBound
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH9
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterSirkEndToEnd
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSirkPerSystemFlowBound
open BookProof.EsaClosure
open BookProof.ChapterH4
open BookProof.ChapterH6
open BookProof.ChapterH9
open BookProof.HashimotoShiftInvert
open BookProof.NavierStokesFlow.LagrangianEsa
open BookProof.NavierStokesFlow.LagrangianEsa
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

theorem BookProof.ChapterSirkPerSystemFlowBound.lagrangian_sirk_flow_error_bound {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (L : LagrangianFullData F)
    (hesa : EssentiallySelfAdjointOn L.D (lagrangianCore L)) {γ : ℂ} (hγ : γ.im ≠ 0) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (X : F →L[ℂ] F),
      IsSelfAdjointExtension (lagrangianCore L) A ∧ IsShiftInvertC A γ X ∧
      ‖X‖ ≤ |γ.im|⁻¹ ∧ numRange X ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ ∧
      ∀ (m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] F)
        (s : RationalScheme F (EuclideanSpace ℂ (Fin m))) (C Dmin h : ℝ),
        IsSirkScheme X V (Metric.closedBall (0 : ℂ) |γ.im|⁻¹) C Dmin h m s →
        ∀ (flow : F →L[ℂ] F), flow = s.psiX →
        ∀ v : F, V (V.adjoint v) = v →
          ‖flow v - sirkApprox V s.psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by sorry
