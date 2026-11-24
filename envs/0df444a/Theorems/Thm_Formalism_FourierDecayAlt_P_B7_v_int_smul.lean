-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_v_int_smul
-- name    : Formalism.FourierDecayAlt.P.B7.v_int_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:58:53.985858+00:00
-- url     : https://prove2.me/theorems/d4b4ce62-3cff-4021-bbac-f2d6ff6da1c2
-- title:
--   B7: v int smul
-- statement:
--   The B7 construction uses the v int smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1334-L1338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1334-L1338

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

theorem Formalism.FourierDecayAlt.P.B7.v_int_smul {P E : Type*} [MeasurableSpace P] {μ : Measure P} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : P → E} (hu : Integrable u μ) {ξ : P → ℂ} (hξm : Measurable ξ) (hξ : ∀ p, ‖ξ p‖ = 1) :
    Integrable (fun p => ξ p • u p) μ := by sorry
