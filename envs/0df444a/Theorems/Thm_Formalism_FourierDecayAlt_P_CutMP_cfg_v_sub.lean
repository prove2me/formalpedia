-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_cfg_v_sub
-- name    : Formalism.FourierDecayAlt.P.CutMP.cfg_v_sub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:33:18.166722+00:00
-- url     : https://prove2.me/theorems/2407dc45-d69f-529b-aca1-57b6025f9186
-- title:
--   Cut MP: cfg v sub
-- statement:
--   The Cut MP construction uses the cfg v sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutLam.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutLam.lean#L11-L14

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutLam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
variable (c : Sz.Cfg)

theorem Formalism.FourierDecayAlt.P.CutMP.cfg_v_sub (i : ℕ) : c.v i - c.v (i + 1) = 4 * c.Del := by sorry
