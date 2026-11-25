-- Prove2me | Theorems.Thm_Formalism_HN_hnSum_of
-- name    : Formalism.HN.hnSum_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:09.176821+00:00
-- url     : https://prove2.me/theorems/33d4a805-c535-4d90-b303-1cd027a67153
-- title:
--   HN: hn Sum of
-- statement:
--   The HN construction uses the hn Sum of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PolygonSlopeSum.lean#L195-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PolygonSlopeSum.lean#L195-L256

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
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
universe u v w x

theorem Formalism.HN.hnSum_of (h1 : DegSupermod.{u, v, w}) (h2 : MuChar.{u, v, w}) (h3 : SatBasic.{u, v, w}) :
    HNSum.{u, v, w, x} := by sorry
