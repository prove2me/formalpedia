-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_contOn_of_CkOn
-- name    : Formalism.FourierDecayAlt.P.B7.contOn_of_CkOn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:00:43.753849+00:00
-- url     : https://prove2.me/theorems/2e59be46-2e43-488f-bc53-a8a09d078ca5
-- title:
--   B7: cont On of Ck On
-- statement:
--   The B7 construction uses the cont On of Ck On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L67-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L67-L74

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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.B7.contOn_of_CkOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {F : Mat k r → E}
    (h : CkOn m (GV k r) F) : ContinuousOn F (GV k r) := by sorry
