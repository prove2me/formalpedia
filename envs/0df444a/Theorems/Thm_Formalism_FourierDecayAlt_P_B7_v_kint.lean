-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_v_kint
-- name    : Formalism.FourierDecayAlt.P.B7.v_kint
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:12:00.958098+00:00
-- url     : https://prove2.me/theorems/9adb84cb-fbb0-4a70-9ed1-ff98dd2b8dc6
-- title:
--   B7: v kint
-- statement:
--   The B7 construction uses the v kint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1383-L1416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1383-L1416

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

theorem Formalism.FourierDecayAlt.P.B7.v_kint {P E : Type*} [MeasurableSpace P] {μ : Measure P} [SFinite μ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (S : P → Prop) (hS : ∀ᵐ p ∂μ, S p) (T : P → P → P)
    (hT : ∀ p, S p → MeasurePreserving (T p) μ μ) (hTe : ∀ p, S p → MeasurableEmbedding (T p))
    (u : P → E) (hu : Integrable u μ)
    (k : P → P → ℂ) (hk : ∀ p p', S p → S p' → inner ℂ (u p) (u (T p p')) = k p p')
    (hkm : AEStronglyMeasurable (fun a : P × P => k a.1 a.2) (μ.prod μ)) :
    Integrable (fun a : P × P => k a.1 a.2) (μ.prod μ) := by sorry
