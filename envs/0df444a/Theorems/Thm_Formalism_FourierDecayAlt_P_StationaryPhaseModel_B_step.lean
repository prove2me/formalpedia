-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_step
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:59.146795+00:00
-- url     : https://prove2.me/theorems/1c12e5a2-a649-49bd-b363-a6b79bc90b2c
-- title:
--   Stationary Phase Model: B step
-- statement:
--   The Stationary Phase Model construction uses the B step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L502-L619
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L502-L619

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_step (ι : Type) [Fintype ι] (N : ℕ) (Γ c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ C₁ : ℝ, 0 ≤ C₁ ∧
    ∀ (v : ι → E), (∀ l, ‖v l‖ = 1) → ∀ (A : Set E) (w : E → ℝ) (φ : E → ℝ) (τ : ℝ), 0 < τ →
      (∀ x ∈ A, 0 < w x) → (∀ x ∈ A, τ ≤ w x ^ 2) → ContDiff ℝ 1 φ → Sym A w 1 (N + 1) Γ (fderiv ℝ φ) →
      (∀ x ∈ A, c₀ * w x ^ 2 ≤ ∑ l, (fderiv ℝ φ x (v l)) ^ 2 + τ) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (b : E → V) (m : ℤ) (K : ℝ),
        HasCompactSupport b → tsupport b ⊆ A → Sym A w m (N + 1) K b →
        ∃ b' : E → V, HasCompactSupport b' ∧ tsupport b' ⊆ A ∧ Sym A w (m - 2) N (C₁ * τ * K) b' ∧
          ∫ x, osc φ τ x • b x ∂μ = ∫ x, osc φ τ x • b' x ∂μ := by sorry
