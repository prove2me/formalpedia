-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_bp_pos
-- name    : Formalism.FourierDecayAlt.P.Sz4.bp_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:29.006477+00:00
-- url     : https://prove2.me/theorems/c07edc4e-67c0-444c-9c98-89cf06b011ef
-- title:
--   Sz4: bp pos
-- statement:
--   The Sz4 construction uses the bp pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L510-L512
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L510-L512

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz4.bp_pos (c : Cfg) (hc : c.Ok) (ht : c.top = true) : 0 < c.bp := by sorry
