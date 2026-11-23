-- Prove2me | Theorems.Thm_Formalism_HN_PolygonExample_covol_Lx
-- name    : Formalism.HN.PolygonExample.covol_Lx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:36.887727+00:00
-- url     : https://prove2.me/theorems/7853b1e1-e855-4b68-82b4-442a76049ad3
-- title:
--   Polygon Example: covol Lx
-- statement:
--   The Polygon Example construction uses the covol Lx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L92-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L92-L103

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

theorem Formalism.HN.PolygonExample.covol_Lx : Formalism.F.covol Lx = 2 := by sorry
