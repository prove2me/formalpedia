-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_uncurry_exp_log_eq_X
-- name    : Formalism.L2.FormalSeriesBounds.FBChart.uncurry_exp_log_eq_X
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T06:07:55.504403+00:00
-- url     : https://prove2.me/theorems/4bc54c6d-cf8e-5501-9b21-1ed3ddf014f8
-- title:
--   FBChart: uncurry exp log eq X
-- statement:
--   The FBChart construction uses the uncurry exp log eq X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLinearCombination.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLinearCombination.lean#L19-L22

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstVanishingAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLinearCombination
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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

theorem Formalism.L2.FormalSeriesBounds.FBChart.uncurry_exp_log_eq_X (Y : FBChart C V O dd) (i : Fin dd) :
    MvPowerSeries.subst (fun j => un1 (Y.lg j)) (un1 (Y.ex i)) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by sorry
