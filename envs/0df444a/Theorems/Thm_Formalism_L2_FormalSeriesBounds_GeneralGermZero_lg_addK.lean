-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_lg_addK
-- name    : Formalism.L2.FormalSeriesBounds.GeneralGermZero.lg_addK
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:03:32.091821+00:00
-- url     : https://prove2.me/theorems/8622c2bf-3fc6-4e89-8657-bb535e98ed18
-- title:
--   General Germ Zero: lg add K
-- statement:
--   The General Germ Zero construction uses the lg add K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeneralGermZero.lean#L54-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeneralGermZero.lean#L54-L71

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
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
open Formalism.L2.FormalSeriesBounds.GeneralGermZero
open Formalism.IncomingBounds FormalGermZero
variable {C : Type} [Field C] {κ : Type} [Fintype κ]

theorem Formalism.L2.FormalSeriesBounds.GeneralGermZero.lg_addK {σ : Type} (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
    (lg : κ → MvPowerSeries κ C) (hadd : LgAdd F lg) (a b : κ → MvPowerSeries σ C)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) (k : κ) :
    MvPowerSeries.subst (addK F a b) (lg k) = MvPowerSeries.subst a (lg k) + MvPowerSeries.subst b (lg k) := by sorry
