-- Prove2me | Theorems.Thm_Formalism_HN_PolygonExample_rk_Px
-- name    : Formalism.HN.PolygonExample.rk_Px
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:45.32647+00:00
-- url     : https://prove2.me/theorems/ed5c64f3-289f-4cdd-805f-582a5f8f6b91
-- title:
--   Polygon Example: rk Px
-- statement:
--   The Polygon Example construction uses the rk Px property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L115-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L115-L124

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
open Formalism.HN.PolygonExample

theorem Formalism.HN.PolygonExample.rk_Px : Formalism.F.rk Px = 1 := by sorry
