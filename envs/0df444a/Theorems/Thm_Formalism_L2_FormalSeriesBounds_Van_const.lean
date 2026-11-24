-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const
-- name    : Formalism.L2.FormalSeriesBounds.Van.const
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:26.755503+00:00
-- url     : https://prove2.me/theorems/fa6b4b32-1b87-4f72-a167-505b959292ec
-- title:
--   Van: const
-- statement:
--   The Van construction uses the const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L34-L36

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
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

theorem Formalism.L2.FormalSeriesBounds.Van.const {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) : constantCoeff f = 0 := by sorry
