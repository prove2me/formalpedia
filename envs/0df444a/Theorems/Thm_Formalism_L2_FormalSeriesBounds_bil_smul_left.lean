-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_smul_left
-- name    : Formalism.L2.FormalSeriesBounds.bil_smul_left
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:36.181084+00:00
-- url     : https://prove2.me/theorems/35b09af1-3320-466a-ab96-cd211589362b
-- title:
--   Formal Series Bounds: bil smul left
-- statement:
--   The Formal Series Bounds construction uses the bil smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L279-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L279-L288

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

theorem Formalism.L2.FormalSeriesBounds.bil_smul_left (F : PS C 2 dd) (c : C) (w v : Fin dd → C) : bil F (c • w) v = c * bil F w v := by sorry
