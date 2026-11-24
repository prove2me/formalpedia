-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_v_swap
-- name    : Formalism.FourierDecayAlt.P.B7.v_swap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:10:21.451689+00:00
-- url     : https://prove2.me/theorems/6358a76b-b319-4baf-8197-c7079c36aa42
-- title:
--   B7: v swap
-- statement:
--   The B7 construction uses the v swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1418-L1458
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1418-L1458

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.B7.v_swap {P T : Type*} [MeasurableSpace P] [MeasurableSpace T] {μ : Measure P} {ν : Measure T}
    [SFinite μ] [SFinite ν]
    (W : T → ℂ) (hW : Integrable W ν) (ξ : T → P → ℂ) (hξm : Measurable (fun a : T × P => ξ a.1 a.2))
    (hξ : ∀ τ p, ‖ξ τ p‖ = 1)
    (k : P → P → ℂ) (hk : Integrable (fun a : P × P => k a.1 a.2) (μ.prod μ)) :
    Integrable (fun τ => W τ * ∫ p, ∫ p', ξ τ p' * k p p' ∂μ ∂μ) ν ∧
    (∫ τ, W τ * ∫ p, ∫ p', ξ τ p' * k p p' ∂μ ∂μ ∂ν) =
      ∫ p, ∫ p', (∫ τ, W τ * ξ τ p' ∂ν) * k p p' ∂μ ∂μ := by sorry
