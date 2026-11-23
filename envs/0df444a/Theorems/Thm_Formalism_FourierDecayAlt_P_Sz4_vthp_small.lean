-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vthp_small
-- name    : Formalism.FourierDecayAlt.P.Sz4.vthp_small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:39.656923+00:00
-- url     : https://prove2.me/theorems/92dac74b-3c2f-411a-adae-70e4798c7510
-- title:
--   Sz4: vthp small
-- statement:
--   The Sz4 construction uses the vthp small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L657-L669
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L657-L669

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

theorem Formalism.FourierDecayAlt.P.Sz4.vthp_small (c : Cfg) (hc : c.Ok) (hv : c.vth ≤ 1 / 10) (ht : c.top = true) :
    c.vthp ≤ 1 / 10 := by sorry
