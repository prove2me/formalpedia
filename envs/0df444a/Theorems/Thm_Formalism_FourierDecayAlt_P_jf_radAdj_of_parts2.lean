-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_jf_radAdj_of_parts2
-- name    : Formalism.FourierDecayAlt.P.jf_radAdj_of_parts2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:46:48.413653+00:00
-- url     : https://prove2.me/theorems/74841a45-d1c6-4a1e-9a1d-f3e544c66623
-- title:
--   P: jf rad Adj of parts2
-- statement:
--   The P construction uses the jf rad Adj of parts2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfBetaAdjCOfLemmaBNorm.lean#L157-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfBetaAdjCOfLemmaBNorm.lean#L157-L159

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfBetaAdjCOfLemmaBNorm
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

theorem Formalism.FourierDecayAlt.P.jf_radAdj_of_parts2 : Formalism.FourierDecayAlt.P.JFxG.Exhaust → Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.P.JFxG.JThetaAdjC →
    Formalism.FourierDecayAlt.B2.LemmaBNorm → Formalism.FourierDecayAlt.JF.RadAdj := by sorry
