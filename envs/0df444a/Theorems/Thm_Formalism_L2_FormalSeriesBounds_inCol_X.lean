-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_inCol_X
-- name    : Formalism.L2.FormalSeriesBounds.inCol_X
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:02.292258+00:00
-- url     : https://prove2.me/theorems/d0525c36-f204-4622-877d-fec234c3d8d3
-- title:
--   Formal Series Bounds: in Col X
-- statement:
--   The Formal Series Bounds construction uses the in Col X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePCartSelfSt.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePCartSelfSt.lean#L36-L38

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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

theorem Formalism.L2.FormalSeriesBounds.inCol_X (col : Fin 2) (i : Fin dd) : inCol col (X i : MvPowerSeries (Fin dd) C) = X (col, i) := by sorry
