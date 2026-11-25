-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_smul_right
-- name    : Formalism.L2.FormalSeriesBounds.bil_smul_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:06.825181+00:00
-- url     : https://prove2.me/theorems/7bda4fd6-6226-4239-b785-45662cd98da8
-- title:
--   Formal Series Bounds: bil smul right
-- statement:
--   The Formal Series Bounds construction uses the bil smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L290-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L290-L299

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

theorem Formalism.L2.FormalSeriesBounds.bil_smul_right (F : PS C 2 dd) (c : C) (w v : Fin dd → C) : bil F w (c • v) = c * bil F w v := by sorry
