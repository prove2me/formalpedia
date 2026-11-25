-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_mul_left
-- name    : Formalism.L2.FormalSeriesBounds.Van.mul_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:46:58.527894+00:00
-- url     : https://prove2.me/theorems/aa42755c-86e2-41a2-955f-1fdfefbe60c2
-- title:
--   Van: mul left
-- statement:
--   The Van construction uses the mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L22-L24

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

theorem Formalism.L2.FormalSeriesBounds.Van.mul_left {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) (g : MvPowerSeries τ C) : Van T (g * f) := by sorry
