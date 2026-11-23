-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_a_sub_ulast_pos
-- name    : Formalism.FourierDecayAlt.P.Sz4.a_sub_ulast_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:59.057893+00:00
-- url     : https://prove2.me/theorems/27a2990c-b00e-4412-afbd-b15dcc47a945
-- title:
--   Sz4: a sub ulast pos
-- statement:
--   The Sz4 construction uses the a sub ulast pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L600-L612
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L600-L612

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

theorem Formalism.FourierDecayAlt.P.Sz4.a_sub_ulast_pos (c : Cfg) (hc : c.Ok) : 0 < c.a - c.ulast := by sorry
