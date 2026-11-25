-- Prove2me | Theorems.Thm_Formalism_HN_slopeIneq_of
-- name    : Formalism.HN.slopeIneq_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:25.681993+00:00
-- url     : https://prove2.me/theorems/4b76b3e8-c7f8-4981-b741-11ed532866da
-- title:
--   HN: slope Ineq of
-- statement:
--   The HN construction uses the slope Ineq of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean#L306-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean#L306-L505

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe uR uV uW uE uF

theorem Formalism.HN.slopeIneq_of (hmV : MuChar.{uR, uV, uE}) (hmW : MuChar.{uR, uW, uF})
    (hs : SatR.{uR, uW, uF}) (hbV : SatBasic.{uR, uV, uE}) (hbW : SatBasic.{uR, uW, uF}) :
    SlopeIneq.{uR, uV, uW, uE, uF} := by sorry
