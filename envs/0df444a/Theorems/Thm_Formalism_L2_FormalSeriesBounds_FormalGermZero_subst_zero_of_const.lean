-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_subst_zero_of_const
-- name    : Formalism.L2.FormalSeriesBounds.FormalGermZero.subst_zero_of_const
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:56:26.576148+00:00
-- url     : https://prove2.me/theorems/e2f82e7f-eeee-4f22-995a-791c5e143c17
-- title:
--   Formal Germ Zero: subst zero of const
-- statement:
--   The Formal Germ Zero construction uses the subst zero of const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L125-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L125-L139

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

theorem Formalism.L2.FormalSeriesBounds.FormalGermZero.subst_zero_of_const {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (0 : σ → MvPowerSeries τ C) f = 0 := by sorry
