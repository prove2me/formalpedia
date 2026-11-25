-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_expS
-- name    : Formalism.L2.FormalSeriesBounds.bil_expS
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:51.541797+00:00
-- url     : https://prove2.me/theorems/35d3c541-cfcb-4a7b-89b4-d21466f98b81
-- title:
--   Formal Series Bounds: bil exp S
-- statement:
--   The Formal Series Bounds construction uses the bil exp S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L488-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L488-L505

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

theorem Formalism.L2.FormalSeriesBounds.bil_expS {f : PS C 2 dd} (hf : Van (Tg dd 0) f) (w v : Fin dd → C) : bil (FB.expS C f) w v = bil f w v := by sorry
