-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_isT_sum
-- name    : Formalism.L2.FormalSeriesBounds.FormalGermZero.isT_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:55:29.795574+00:00
-- url     : https://prove2.me/theorems/e127c1a7-2277-40ad-946f-73c3afb035f4
-- title:
--   Formal Germ Zero: is T sum
-- statement:
--   The Formal Germ Zero construction uses the is T sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L201-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L201-L245

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
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
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.FormalGermZero.isT_sum {V : VF C} {d : ℕ} {I₁ J₁ : Type} [Fintype I₁] [Fintype J₁] {X₁ : Cart V d I₁ J₁} (S : Sys X₁)
    {t : I₁ → MvPowerSeries I₁ C} (ht : S.IsT t) (x : I₁) :
    ∑ c, PowerSeries.subst (t c) (tyS V.l (fun s => S.al c s x)) = MvPowerSeries.X x := by sorry
