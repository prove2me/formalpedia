-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_pair_int
-- name    : Formalism.L2.FormalSeriesBounds.FormalGermZero.pair_int
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:56:39.364059+00:00
-- url     : https://prove2.me/theorems/6fa3e8b3-8f16-4c70-b5b2-13e1c586f685
-- title:
--   Formal Germ Zero: pair int
-- statement:
--   The Formal Germ Zero construction uses the pair int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L265-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L265-L268

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
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

theorem Formalism.L2.FormalSeriesBounds.FormalGermZero.pair_int {V : VF C} {σ : Type} {a b : Fin dd → MvPowerSeries σ C} (ha : ∀ j, IntS V (a j))
    (hb : ∀ j, IntS V (b j)) : ∀ q : Fin 2 × Fin dd, IntS V (![a, b] q.1 q.2) := by sorry
