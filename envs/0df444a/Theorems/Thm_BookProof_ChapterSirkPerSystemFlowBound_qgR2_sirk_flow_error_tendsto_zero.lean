-- Prove2me | Theorems.Thm_BookProof_ChapterSirkPerSystemFlowBound_qgR2_sirk_flow_error_tendsto_zero
-- name    : BookProof.ChapterSirkPerSystemFlowBound.qgR2_sirk_flow_error_tendsto_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-02T09:32:15.462386+00:00
-- url     : https://prove2.me/theorems/3e73c23c-41fa-44f8-92b5-049e62f9e69b
-- title:
--   `BookProof.ChapterSirkPerSystemFlowBound.qgR2_sirk_flow_error_tendsto_zero` (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ) {γ : ℂ} (hγ : γ.im ≠ 0) : ∃ (Dom : Submodule ℂ L2Nat)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkPerSystemFlowBound`.
--
--   `BookProof.ChapterSirkPerSystemFlowBound.qgR2_sirk_flow_error_tendsto_zero` (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ) {γ : ℂ} (hγ : γ.im ≠ 0) : ∃ (Dom : Submodule ℂ L2Nat) (A : Dom →ₗ[ℂ] L2Nat) (X : L2Nat →L[ℂ] L2Nat), IsSelfAdjointExtension (qgR2ModeHamiltonian a b M alpha Rc) A ∧ IsShiftInvertC A γ X ∧ numRange X ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ ∧ ∀ (V : ∀ m : ℕ, EuclideanSpace ℂ (Fin m) →L[ℂ] L2Nat) (s : ∀ m : ℕ, RationalScheme L2Nat (EuclideanSpace ℂ (Fin m))) (C Dmin h : ℝ), 0 < h → (∀ m, IsSirkScheme X (V m) (Metric.closedBall (0 : ℂ) |γ.im|⁻¹) C Dmin h m (s m)) → ∀ (flow : L2Nat →L[ℂ] L2Nat), (∀ m, flow = (s m).psiX) → ∀ v : L2Nat, (∀ m, V m ((V m).adjoint v) = v) → Tendsto (fun m => ‖flow v - sirkApprox (V m) (s m).psiB v‖) atTop (𝓝 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSirkPerSystemFlowBound.qgR2_sirk_flow_error_tendsto_zero`.

-- Generated from ChapterSirkPerSystemFlowBound.lean — theorem BookProof.ChapterSirkPerSystemFlowBound.qgR2_sirk_flow_error_tendsto_zero
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterSirkSpectralGeometry
import Definitions.Def_ChapterSirkPerSystem
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
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
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH9
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkEndToEnd
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSirkEndToEnd
import Definitions.Def_ChapterSirkPerSystemFlowBound
open BookProof.EsaClosure
open BookProof.FarisLavine
open BookProof.ChapterH4
open BookProof.ChapterH9
open BookProof.HashimotoShiftInvert
open BookProof.QuantumGravityDensitized
open BookProof.ChapterSirkEndToEnd
open BookProof.Starobinsky
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

theorem BookProof.ChapterSirkPerSystemFlowBound.qgR2_sirk_flow_error_tendsto_zero (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ)
    {γ : ℂ} (hγ : γ.im ≠ 0) :
    ∃ (Dom : Submodule ℂ L2Nat) (A : Dom →ₗ[ℂ] L2Nat) (X : L2Nat →L[ℂ] L2Nat),
      IsSelfAdjointExtension (qgR2ModeHamiltonian a b M alpha Rc) A ∧
      IsShiftInvertC A γ X ∧ numRange X ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ ∧
      ∀ (V : ∀ m : ℕ, EuclideanSpace ℂ (Fin m) →L[ℂ] L2Nat)
        (s : ∀ m : ℕ, RationalScheme L2Nat (EuclideanSpace ℂ (Fin m))) (C Dmin h : ℝ),
        0 < h →
        (∀ m, IsSirkScheme X (V m) (Metric.closedBall (0 : ℂ) |γ.im|⁻¹) C Dmin h m (s m)) →
        ∀ (flow : L2Nat →L[ℂ] L2Nat), (∀ m, flow = (s m).psiX) →
        ∀ v : L2Nat, (∀ m, V m ((V m).adjoint v) = v) →
          Tendsto (fun m => ‖flow v - sirkApprox (V m) (s m).psiB v‖) atTop (𝓝 0) := by sorry
