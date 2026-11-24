-- Prove2me | Theorems.Thm_Formalism_HN_map_range_toIntLinearMap
-- name    : Formalism.HN.map_range_toIntLinearMap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:24.235939+00:00
-- url     : https://prove2.me/theorems/53ebdb38-2a65-4aed-92ef-1e03db06dc8b
-- title:
--   HN: map range to Int Linear Map
-- statement:
--   The HN construction uses the map range to Int Linear Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean#L218-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean#L218-L227

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem Formalism.HN.map_range_toIntLinearMap {G : Type*} [AddCommGroup G] (α : G →+ E) (p : E →L[ℝ] E) :
    (LinearMap.range α.toIntLinearMap).map (p.toLinearMap.restrictScalars ℤ) =
      LinearMap.range ((p.toLinearMap.toAddMonoidHom.comp α).toIntLinearMap) := by sorry
