-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff1_of_lgLin
-- name    : Formalism.L2.FormalSeriesBounds.coeff1_of_lgLin
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-27T06:01:56.536803+00:00
-- url     : https://prove2.me/theorems/08873c5c-d7c8-5bcd-9b7a-2b5f94673d17
-- title:
--   Formal Series Bounds: coeff1 of lg Lin
-- statement:
--   The Formal Series Bounds construction uses the coeff1 of lg Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLinearCombination.lean#L103-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLinearCombination.lean#L103-L113

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstVanishingAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLinearCombination
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.coeff1_of_lgLin (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} {U : Fin dd → C} (hγ : IsCv V γ)
    (hlg : Y.LgLin γ U) (i : Fin dd) : PowerSeries.coeff 1 (γ i) = U i := by sorry
