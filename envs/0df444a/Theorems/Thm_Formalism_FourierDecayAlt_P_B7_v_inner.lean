-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_v_inner
-- name    : Formalism.FourierDecayAlt.P.B7.v_inner
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:09:42.818116+00:00
-- url     : https://prove2.me/theorems/a413f489-10af-4c9f-9fd7-1acc102b52b8
-- title:
--   B7: v inner
-- statement:
--   The B7 construction uses the v inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1340-L1361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1340-L1361

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

theorem Formalism.FourierDecayAlt.P.B7.v_inner {P E : Type*} [MeasurableSpace P] {μ : Measure P} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (S : P → Prop) (hS : ∀ᵐ p ∂μ, S p) (T : P → P → P)
    (hT : ∀ p, S p → MeasurePreserving (T p) μ μ) (hTe : ∀ p, S p → MeasurableEmbedding (T p))
    (u : P → E) (hu : Integrable u μ) (ξ : P → ℂ) (hξm : Measurable ξ) (hξ : ∀ p, ‖ξ p‖ = 1)
    (hξT : ∀ p p', S p → S p' → ξ (T p p') = ξ p * ξ p')
    (k : P → P → ℂ) (hk : ∀ p p', S p → S p' → inner ℂ (u p) (u (T p p')) = k p p')
    (p : P) (hp : S p) :
    inner ℂ (u p) (∫ p', ξ p' • u p' ∂μ) = ξ p * ∫ p', ξ p' * k p p' ∂μ := by sorry
