-- Prove2me | Theorems.Thm_Formalism_HN_hnStep_of
-- name    : Formalism.HN.hnStep_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:03.929826+00:00
-- url     : https://prove2.me/theorems/963ac0df-fd48-4b28-9ba2-9dcc1bc14dbc
-- title:
--   HN: hn Step of
-- statement:
--   The HN construction uses the hn Step of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HNStep.lean#L18-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HNStep.lean#L18-L155

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
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

theorem Formalism.HN.hnStep_of (h1 : DegSupermod.{u, v, w}) (h2 : MuChar.{u, v, w}) (h3 : RatioMax.{u, v, w})
    (h4 : FinSup.{u, v, w}) (h5 : SatR.{u, v, w}) (h6 : SatBasic.{u, v, w}) :
    HNStep.{u, v, w} := by sorry
