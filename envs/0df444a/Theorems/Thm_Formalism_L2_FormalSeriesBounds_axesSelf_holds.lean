-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_axesSelf_holds
-- name    : Formalism.L2.FormalSeriesBounds.axesSelf_holds
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:53.21153+00:00
-- url     : https://prove2.me/theorems/f7f4a39e-e040-4c10-9f26-eb7bc1bdd1f4
-- title:
--   Formal Series Bounds: axes Self holds
-- statement:
--   The Formal Series Bounds construction uses the axes Self holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePAxesSelfSt.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePAxesSelfSt.lean#L82-L92

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.axesSelf_holds : AxesSelfSt := by sorry
