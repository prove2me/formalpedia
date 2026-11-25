-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_univ
-- name    : Formalism.L2.FormalSeriesBounds.van_univ
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:14:19.837034+00:00
-- url     : https://prove2.me/theorems/4aea1a13-f34a-4efe-a774-ecc7d1163d44
-- title:
--   Formal Series Bounds: van univ
-- statement:
--   The Formal Series Bounds construction uses the van univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L54-L62

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.van_univ {τ : Type} {f : MvPowerSeries τ C} (h : MvPowerSeries.constantCoeff f = 0) :
    Van Set.univ f := by sorry
