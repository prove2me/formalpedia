-- Prove2me | Theorems.Thm_Formalism_HN_PolygonExample_rk_Lx
-- name    : Formalism.HN.PolygonExample.rk_Lx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:14.009175+00:00
-- url     : https://prove2.me/theorems/ccacdf51-dadd-4f7d-b62c-704c2b1807b4
-- title:
--   Polygon Example: rk Lx
-- statement:
--   The Polygon Example construction uses the rk Lx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L88-L90

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

theorem Formalism.HN.PolygonExample.rk_Lx : Formalism.F.rk Lx = 2 := by sorry
