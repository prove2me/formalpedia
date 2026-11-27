-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Agr_trans
-- name    : Formalism.L2.FormalSeriesBounds.Agr.trans
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:24:01.92712+00:00
-- url     : https://prove2.me/theorems/62561ce3-13ea-518a-a6a5-cd9e33cd52c5
-- title:
--   Agr: trans
-- statement:
--   The Agr construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L25-L26

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.Agr.trans {τ : Type} {k : ℕ} {f g g' : MvPowerSeries τ C} (h : Agr k f g) (h' : Agr k g g') : Agr k f g' := by sorry
