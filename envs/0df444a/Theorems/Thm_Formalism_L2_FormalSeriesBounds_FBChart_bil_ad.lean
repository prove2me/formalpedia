-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_bil_ad
-- name    : Formalism.L2.FormalSeriesBounds.FBChart.bil_ad
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:51:15.783903+00:00
-- url     : https://prove2.me/theorems/62659dd7-7862-42ce-90d5-804ebfac7b90
-- title:
--   FBChart: bil ad
-- statement:
--   The FBChart construction uses the bil ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L507-L515
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L507-L515

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
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

theorem Formalism.L2.FormalSeriesBounds.FBChart.bil_ad (Y : FBChart C V O dd) (a : O) (w v : Fin dd → C) :
    bil (Y.B.ad a) w v = bil Y.h (linAct (Y.B.A.act a) w) v - bil Y.h w (linAct (Y.B.A.act (star a)) v) := by sorry
