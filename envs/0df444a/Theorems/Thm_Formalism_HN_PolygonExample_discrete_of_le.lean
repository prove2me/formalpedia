-- Prove2me | Theorems.Thm_Formalism_HN_PolygonExample_discrete_of_le
-- name    : Formalism.HN.PolygonExample.discrete_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:42.147833+00:00
-- url     : https://prove2.me/theorems/d6e474dd-f5e5-41dc-b56e-8efb803e2cfb
-- title:
--   Polygon Example: discrete of le
-- statement:
--   The Polygon Example construction uses the discrete of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L57-L64

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

theorem Formalism.HN.PolygonExample.discrete_of_le (N : Submodule ℤ E2) (hN : N ≤ Lx) : DiscreteTopology N := by sorry
