-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_Tn_mp
-- name    : Formalism.FourierDecayAlt.P.B2x8.Tn_mp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:58:06.334794+00:00
-- url     : https://prove2.me/theorems/d3fde210-66bf-4fa4-b42b-68f440ceace5
-- title:
--   B2x8: Tn mp
-- statement:
--   The B2x8 construction uses the Tn mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L796-L824
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L796-L824

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x8.Tn_mp (x₀ : HPar k r') :
    MeasurePreserving (Tn k r' x₀) (μx.prod (volume : Measure (HPar k r'))) (μx.prod (volume : Measure (HPar k r'))) := by sorry
