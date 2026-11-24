-- Prove2me | Theorems.Thm_Formalism_HN_hnExtreme_of
-- name    : Formalism.HN.hnExtreme_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:34.362015+00:00
-- url     : https://prove2.me/theorems/29a6f373-9354-4ee1-8714-7eca047fccf5
-- title:
--   HN: hn Extreme of
-- statement:
--   The HN construction uses the hn Extreme of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HNExtreme.lean#L25-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HNExtreme.lean#L25-L112

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Lemmata_GeneralBFactLeftForm_Imports
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNExtreme
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
universe u v w

theorem Formalism.HN.hnExtreme_of (h1 : HNSlopes.{u, v, w}) (h2 : MuChar.{u, v, w}) (h3 : HNStep.{u, v, w})
    (h4 : SatBasic.{u, v, w}) : HNExtreme.{u, v, w} := by sorry
