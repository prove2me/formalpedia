-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_elementary_pair_support
-- name    : Formalism.L2.FormalSeriesBounds.elementary_pair_support
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:35.358747+00:00
-- url     : https://prove2.me/theorems/c5685549-ee7f-4acd-9b77-e4aba8099c58
-- title:
--   Formal Series Bounds: elementary pair support
-- statement:
--   The Formal Series Bounds construction uses the elementary pair support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L71-L74

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
variable {τ : Type}

theorem Formalism.L2.FormalSeriesBounds.elementary_pair_support {P Q s : τ} (h : E2 P Q s ≠ 0) : s = P ∨ s = Q := by sorry
