-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_kDel_pos
-- name    : Formalism.FourierDecayAlt.P.Sz4.kDel_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:17:21.412592+00:00
-- url     : https://prove2.me/theorems/cf5bd8ca-0af4-4747-b86a-509b0b908df3
-- title:
--   Sz4: k Del pos
-- statement:
--   The Sz4 construction uses the k Del pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L479-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L479-L482

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

theorem Formalism.FourierDecayAlt.P.Sz4.kDel_pos (c : Cfg) (hc : c.Ok) : 0 < 4 * (c.k : ℝ) * c.Del := by sorry
