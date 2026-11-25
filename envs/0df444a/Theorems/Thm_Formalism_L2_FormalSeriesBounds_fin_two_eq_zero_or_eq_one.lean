-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_fin_two_eq_zero_or_eq_one
-- name    : Formalism.L2.FormalSeriesBounds.fin_two_eq_zero_or_eq_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:44:42.02677+00:00
-- url     : https://prove2.me/theorems/89b2020a-3d25-4919-9455-352b61508ea2
-- title:
--   Formal Series Bounds: fin two eq zero or eq one
-- statement:
--   The Formal Series Bounds construction uses the fin two eq zero or eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L444-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L444-L444

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

theorem Formalism.L2.FormalSeriesBounds.fin_two_eq_zero_or_eq_one : ∀ x : Fin 2, x = 0 ∨ x = 1 := by sorry
