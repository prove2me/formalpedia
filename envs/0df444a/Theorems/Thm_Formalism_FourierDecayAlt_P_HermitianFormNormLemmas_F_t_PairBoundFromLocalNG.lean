-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_F_t_PairBoundFromLocalNG
-- name    : Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F.t_PairBoundFromLocalNG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:48.040955+00:00
-- url     : https://prove2.me/theorems/98837373-58d7-41e2-a81d-f4fccbb9184d
-- title:
--   F: t Pair Bound From Local NG
-- statement:
--   The F construction uses the t Pair Bound From Local NG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L1076-L1106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L1076-L1106

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset NumberField
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN

theorem Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F.t_PairBoundFromLocalNG : PairBoundFromLocalNG := by sorry
