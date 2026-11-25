-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_lg_addS
-- name    : Formalism.L2.FormalSeriesBounds.FormalGermZero.lg_addS
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:56:50.771801+00:00
-- url     : https://prove2.me/theorems/02636cf0-e3f0-4053-b689-0265d17189fb
-- title:
--   Formal Germ Zero: lg add S
-- statement:
--   The Formal Germ Zero construction uses the lg add S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L326-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L326-L361

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem Formalism.L2.FormalSeriesBounds.FormalGermZero.lg_addS {σ : Type} (Y : FBChart C V O dd) (a b : Fin dd → MvPowerSeries σ C)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0)
    (i : Fin dd) :
    MvPowerSeries.subst (addS Y.B.G.F a b) (un1 (Y.lg i)) =
      MvPowerSeries.subst a (un1 (Y.lg i)) + MvPowerSeries.subst b (un1 (Y.lg i)) := by sorry
