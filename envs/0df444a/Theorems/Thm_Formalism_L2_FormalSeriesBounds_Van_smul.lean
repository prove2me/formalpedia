-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_smul
-- name    : Formalism.L2.FormalSeriesBounds.Van.smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:06:50.005245+00:00
-- url     : https://prove2.me/theorems/4ef51114-6494-48d1-9ba5-ba25fe4506c6
-- title:
--   Van: smul
-- statement:
--   The Van construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L38-L40

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

theorem Formalism.L2.FormalSeriesBounds.Van.smul {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) (c : C) : Van T (c • f) := by sorry
