-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_jf_radAdj_of_parts
-- name    : Formalism.FourierDecayAlt.P.jf_radAdj_of_parts
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:34:49.701561+00:00
-- url     : https://prove2.me/theorems/cbcd75f3-693a-4cd9-8efe-be6c0d173643
-- title:
--   P: jf rad Adj of parts
-- statement:
--   The P construction uses the jf rad Adj of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactSupportFiniteClass.lean#L221-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactSupportFiniteClass.lean#L221-L224

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaConjOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.jf_radAdj_of_parts : Formalism.FourierDecayAlt.P.JFxG.Exhaust → Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.P.JFxG.JThetaAdjC →
    Formalism.FourierDecayAlt.P.JFxG.BetaAdjC → Formalism.FourierDecayAlt.JF.RadAdj := by sorry
