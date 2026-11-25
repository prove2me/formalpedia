-- Prove2me | Theorems.Thm_Formalism_HN_muChar_of
-- name    : Formalism.HN.muChar_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:28.497293+00:00
-- url     : https://prove2.me/theorems/4b99f831-bdd0-4972-9a55-f9a0630bce9a
-- title:
--   HN: mu Char of
-- statement:
--   The HN construction uses the mu Char of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/MuChar.lean#L21-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/MuChar.lean#L21-L171

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
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
universe u v w in

theorem Formalism.HN.muChar_of (h1 : SatR.{u, v, w}) (h2 : SatBasic.{u, v, w}) (h3 : RatioMax.{u, v, w}) :
    MuChar.{u, v, w} := by sorry
