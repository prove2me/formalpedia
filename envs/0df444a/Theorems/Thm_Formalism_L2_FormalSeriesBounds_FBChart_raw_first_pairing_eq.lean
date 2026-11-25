-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_raw_first_pairing_eq
-- name    : Formalism.L2.FormalSeriesBounds.FBChart.raw_first_pairing_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:30.417196+00:00
-- url     : https://prove2.me/theorems/ebf60966-e683-4597-ad9a-9f8b3b58a3bf
-- title:
--   FBChart: raw first pairing eq
-- statement:
--   The FBChart construction uses the raw first pairing eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L517-L533
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L517-L533

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

theorem Formalism.L2.FormalSeriesBounds.FBChart.raw_first_pairing_eq (Y : FBChart C V O dd) {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)
    (w v : Fin dd → C) : (Y.raw p).sg1 w v = -bil Y.h w v := by sorry
