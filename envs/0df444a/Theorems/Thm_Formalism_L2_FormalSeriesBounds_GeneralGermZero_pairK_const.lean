-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_pairK_const
-- name    : Formalism.L2.FormalSeriesBounds.GeneralGermZero.pairK_const
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:03:21.91768+00:00
-- url     : https://prove2.me/theorems/16c9929b-ed73-43cf-bcc1-63791ef8a879
-- title:
--   General Germ Zero: pair K const
-- statement:
--   The General Germ Zero construction uses the pair K const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeneralGermZero.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeneralGermZero.lean#L38-L42

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
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

theorem Formalism.L2.FormalSeriesBounds.GeneralGermZero.pairK_const {σ : Type} {a b : κ → MvPowerSeries σ C} (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) :
    ∀ q : Fin 2 × κ, MvPowerSeries.constantCoeff (![a, b] q.1 q.2) = 0 := by sorry
