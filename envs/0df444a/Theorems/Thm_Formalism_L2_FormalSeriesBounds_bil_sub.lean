-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_sub
-- name    : Formalism.L2.FormalSeriesBounds.bil_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:07.114851+00:00
-- url     : https://prove2.me/theorems/8671e0f6-e58a-410a-a1dc-34fe29ceb56f
-- title:
--   Formal Series Bounds: bil sub
-- statement:
--   The Formal Series Bounds construction uses the bil sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L301-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L301-L309

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
variable {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.bil_sub (F G : PS C 2 dd) (w v : Fin dd → C) : bil (F - G) w v = bil F w v - bil G w v := by sorry
