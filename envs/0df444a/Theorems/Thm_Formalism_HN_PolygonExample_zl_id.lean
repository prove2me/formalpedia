-- Prove2me | Theorems.Thm_Formalism_HN_PolygonExample_zl_id
-- name    : Formalism.HN.PolygonExample.zl_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:53.404736+00:00
-- url     : https://prove2.me/theorems/2e35c895-a77f-4a29-be77-09bbcbb3dd05
-- title:
--   Polygon Example: zl id
-- statement:
--   The Polygon Example construction uses the zl id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L21-L23

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

theorem Formalism.HN.PolygonExample.zl_id (N : Submodule ℤ E2) : zl (AddMonoidHom.id E2) N = N := by sorry
