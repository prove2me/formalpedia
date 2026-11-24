-- Prove2me | Theorems.Thm_Formalism_HN_example_of
-- name    : Formalism.HN.example_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:07.120916+00:00
-- url     : https://prove2.me/theorems/2e66539f-5a92-4aa9-97b0-eb57c3ef5002
-- title:
--   HN: example of
-- statement:
--   The HN construction uses the example of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L228-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L228-L349

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
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
open PolygonExample
local notation "ρx" => AddMonoidHom.id E2

theorem Formalism.HN.example_of (h1 : MuChar.{0, 0, 0}) (h2 : HNStep.{0, 0, 0}) (h3 : HNSlopes.{0, 0, 0}) :
    Example := by sorry
