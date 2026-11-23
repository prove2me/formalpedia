-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_v_anti
-- name    : Formalism.FourierDecayAlt.P.Sz4.v_anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:14.423724+00:00
-- url     : https://prove2.me/theorems/0033b874-5fae-4375-bbb0-3b8178b87f01
-- title:
--   Sz4: v anti
-- statement:
--   The Sz4 construction uses the v anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L324-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L324-L328

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

theorem Formalism.FourierDecayAlt.P.Sz4.v_anti (c : Cfg) (hc : c.Ok) (i j : ℕ) (hij : i < j) : c.v j < c.v i := by sorry
