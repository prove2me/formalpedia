-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_v_one_nonneg
-- name    : Formalism.FourierDecayAlt.P.Sz4.v_one_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:18.589662+00:00
-- url     : https://prove2.me/theorems/16c07e5a-3ff6-4f75-8cf0-34c2b4b79d05
-- title:
--   Sz4: v one nonneg
-- statement:
--   The Sz4 construction uses the v one nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L412-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L412-L418

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

theorem Formalism.FourierDecayAlt.P.Sz4.v_one_nonneg (c : Cfg) (hc : c.Ok) : 0 ≤ c.v 1 := by sorry
