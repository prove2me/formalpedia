-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_pairK_int
-- name    : Formalism.L2.FormalSeriesBounds.GeneralGermZero.pairK_int
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:03:50.259913+00:00
-- url     : https://prove2.me/theorems/2f90bd25-7d75-406d-adb9-a8c060832e4d
-- title:
--   General Germ Zero: pair K int
-- statement:
--   The General Germ Zero construction uses the pair K int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeneralGermZero.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeneralGermZero.lean#L44-L47

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

theorem Formalism.L2.FormalSeriesBounds.GeneralGermZero.pairK_int {V : VF C} {σ : Type} {a b : κ → MvPowerSeries σ C} (ha : ∀ j, IntS V (a j))
    (hb : ∀ j, IntS V (b j)) : ∀ q : Fin 2 × κ, IntS V (![a, b] q.1 q.2) := by sorry
