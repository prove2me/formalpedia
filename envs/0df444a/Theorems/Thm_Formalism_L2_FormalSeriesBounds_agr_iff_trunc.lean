-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_agr_iff_trunc
-- name    : Formalism.L2.FormalSeriesBounds.agr_iff_trunc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:12.003388+00:00
-- url     : https://prove2.me/theorems/4ccc56c4-af65-408f-a8ad-2054f9f2eb66
-- title:
--   Formal Series Bounds: agr iff trunc
-- statement:
--   The Formal Series Bounds construction uses the agr iff trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L31-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L31-L42

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

theorem Formalism.L2.FormalSeriesBounds.agr_iff_trunc {τ : Type} [Finite τ] (k : ℕ) (f g : MvPowerSeries τ C) :
    Agr k f g ↔ MvPowerSeries.truncTotal k f = MvPowerSeries.truncTotal k g := by sorry
