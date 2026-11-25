-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_cfg_v_ge_vlast
-- name    : Formalism.FourierDecayAlt.P.CutMP.cfg_v_ge_vlast
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:24:14.94795+00:00
-- url     : https://prove2.me/theorems/533c59d0-595f-5017-b114-ccf35896c7ea
-- title:
--   Cut MP: cfg v ge vlast
-- statement:
--   The Cut MP construction uses the cfg v ge vlast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutLam.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutLam.lean#L16-L21

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

theorem Formalism.FourierDecayAlt.P.CutMP.cfg_v_ge_vlast (hok : c.Ok) (i : ℕ) (hi : i + 1 ≤ c.k) : c.vlast ≤ c.v i := by sorry
