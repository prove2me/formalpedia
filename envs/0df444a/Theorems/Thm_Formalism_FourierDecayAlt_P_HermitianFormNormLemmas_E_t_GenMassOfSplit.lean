-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_E_t_GenMassOfSplit
-- name    : Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E.t_GenMassOfSplit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:49.404325+00:00
-- url     : https://prove2.me/theorems/a120dbc5-fc3d-4509-a8d0-fcdbd69701c9
-- title:
--   E: t Gen Mass Of Split
-- statement:
--   The E construction uses the t Gen Mass Of Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L938-L954
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L938-L954

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open scoped ComplexOrder ComplexConjugate
open Classical

theorem Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E.t_GenMassOfSplit : Formalism.FourierDecayAlt.PN.GenMassOfSplit := by sorry
