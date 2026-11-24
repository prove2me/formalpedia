-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_jf_betaAdjC_of_lemmaBNorm
-- name    : Formalism.FourierDecayAlt.P.jf_betaAdjC_of_lemmaBNorm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:46:31.293578+00:00
-- url     : https://prove2.me/theorems/04c80220-5d76-4d71-820b-1bd42ee68ebc
-- title:
--   P: jf beta Adj C of lemma BNorm
-- statement:
--   The P construction uses the jf beta Adj C of lemma BNorm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfBetaAdjCOfLemmaBNorm.lean#L77-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfBetaAdjCOfLemmaBNorm.lean#L77-L155

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

theorem Formalism.FourierDecayAlt.P.jf_betaAdjC_of_lemmaBNorm : Formalism.FourierDecayAlt.B2.LemmaBNorm → Formalism.FourierDecayAlt.P.JFxG.BetaAdjC := by sorry
