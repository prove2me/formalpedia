-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_v_normsq
-- name    : Formalism.FourierDecayAlt.P.B7.v_normsq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:10:44.952781+00:00
-- url     : https://prove2.me/theorems/fb92f97a-2190-4fa6-a954-f09fd064c707
-- title:
--   B7: v normsq
-- statement:
--   The B7 construction uses the v normsq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1363-L1381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1363-L1381

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

theorem Formalism.FourierDecayAlt.P.B7.v_normsq {P E : Type*} [MeasurableSpace P] {μ : Measure P} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (S : P → Prop) (hS : ∀ᵐ p ∂μ, S p) (T : P → P → P)
    (hT : ∀ p, S p → MeasurePreserving (T p) μ μ) (hTe : ∀ p, S p → MeasurableEmbedding (T p))
    (u : P → E) (hu : Integrable u μ) (ξ : P → ℂ) (hξm : Measurable ξ) (hξ : ∀ p, ‖ξ p‖ = 1)
    (hξT : ∀ p p', S p → S p' → ξ (T p p') = ξ p * ξ p')
    (k : P → P → ℂ) (hk : ∀ p p', S p → S p' → inner ℂ (u p) (u (T p p')) = k p p') :
    (((‖∫ p, ξ p • u p ∂μ‖ ^ 2 : ℝ)) : ℂ) = ∫ p, ∫ p', ξ p' * k p p' ∂μ ∂μ := by sorry
