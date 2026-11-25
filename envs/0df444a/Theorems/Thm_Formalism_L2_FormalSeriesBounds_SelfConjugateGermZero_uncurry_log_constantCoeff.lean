-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_uncurry_log_constantCoeff
-- name    : Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.uncurry_log_constantCoeff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:20:41.503689+00:00
-- url     : https://prove2.me/theorems/68a932f7-616a-4b6f-8bae-9d312be12741
-- title:
--   Self Conjugate Germ Zero: uncurry log constant Coeff
-- statement:
--   The Self Conjugate Germ Zero construction uses the uncurry log constant Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLogConstantCoeff.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLogConstantCoeff.lean#L55-L58

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
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
open Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ FormalGermZero GeneralGermZero
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.uncurry_log_constantCoeff (Y : FBChart C V O dd) (j : Fin dd) : MvPowerSeries.constantCoeff (un1 (Y.lg j)) = 0 := by sorry
