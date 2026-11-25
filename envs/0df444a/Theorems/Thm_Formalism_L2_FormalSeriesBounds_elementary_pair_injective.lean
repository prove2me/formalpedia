-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_elementary_pair_injective
-- name    : Formalism.L2.FormalSeriesBounds.elementary_pair_injective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:54.59916+00:00
-- url     : https://prove2.me/theorems/9e5030df-1b92-4d6f-84f9-715cd19ed961
-- title:
--   Formal Series Bounds: elementary pair injective
-- statement:
--   The Formal Series Bounds construction uses the elementary pair injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L140-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L140-L155

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {τ κ : Type} [Fintype κ]

theorem Formalism.L2.FormalSeriesBounds.elementary_pair_injective {i i' j j' : κ} (h : E2 ((0 : Fin 2), i) ((1 : Fin 2), j) = E2 ((0 : Fin 2), i') ((1 : Fin 2), j')) :
    i = i' ∧ j = j' := by sorry
