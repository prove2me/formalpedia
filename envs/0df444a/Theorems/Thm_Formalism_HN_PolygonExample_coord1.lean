-- Prove2me | Theorems.Thm_Formalism_HN_PolygonExample_coord1
-- name    : Formalism.HN.PolygonExample.coord1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:56.975847+00:00
-- url     : https://prove2.me/theorems/e6f2693b-dc60-4deb-8686-05aeeb6af9ee
-- title:
--   Polygon Example: coord1
-- statement:
--   The Polygon Example construction uses the coord1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L28-L30

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

theorem Formalism.HN.PolygonExample.coord1 (m n : ℤ) : (m • e₀ + n • ((2 : ℝ) • e₁)) 1 = 2 * n := by sorry
