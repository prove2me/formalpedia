-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ne01
-- name    : Formalism.L2.FormalSeriesBounds.ne01
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:04.962309+00:00
-- url     : https://prove2.me/theorems/94969150-0725-448f-be0b-980ae1a1d2d5
-- title:
--   Formal Series Bounds: ne01
-- statement:
--   The Formal Series Bounds construction uses the ne01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L348-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L348-L350

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

theorem Formalism.L2.FormalSeriesBounds.ne01 (x y : Fin dd) : ((0 : Fin 2), x) ≠ ((1 : Fin 2), y) := by sorry
