-- Prove2me | Theorems.Thm_Formalism_HN_DualPolygon_ht_alg
-- name    : Formalism.HN.DualPolygon.ht_alg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:03.458998+00:00
-- url     : https://prove2.me/theorems/de7f213b-7a48-47b3-86f3-b0582d328b7b
-- title:
--   Dual Polygon: ht alg
-- statement:
--   The Dual Polygon construction uses the ht alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DualPl.lean#L1017-L1024
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DualPl.lean#L1017-L1024

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN

theorem Formalism.HN.DualPolygon.ht_alg (f r j : ℕ) (D u cR cL cS : ℝ) (hu : u ^ 2 * D = 1)
    (h : cR * cL * 2 ^ (2 * f * r) = D ^ r * cS) :
    2 ^ (f * r) * u ^ r * cR * (2 ^ (f * (r + j)) * u ^ (r + j) * cL) =
      2 ^ (f * j) * u ^ j * cS := by sorry
