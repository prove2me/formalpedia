-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_col_inj
-- name    : Formalism.L2.FormalSeriesBounds.col_inj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:32.539895+00:00
-- url     : https://prove2.me/theorems/465032cb-7ea8-41a1-b489-5a994ec73c11
-- title:
--   Formal Series Bounds: col inj
-- statement:
--   The Formal Series Bounds construction uses the col inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePCartSelfSt.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePCartSelfSt.lean#L23-L24

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
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

theorem Formalism.L2.FormalSeriesBounds.col_inj (col : Fin 2) : Function.Injective (fun x : Fin dd => (col, x)) := by sorry
