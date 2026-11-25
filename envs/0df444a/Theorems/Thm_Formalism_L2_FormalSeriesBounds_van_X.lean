-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_X
-- name    : Formalism.L2.FormalSeriesBounds.van_X
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:00.297231+00:00
-- url     : https://prove2.me/theorems/7e751c5a-68f7-4b9a-b911-108282faceae
-- title:
--   Formal Series Bounds: van X
-- statement:
--   The Formal Series Bounds construction uses the van X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L270-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L270-L274

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
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

theorem Formalism.L2.FormalSeriesBounds.van_X {τ : Type} {T : Set τ} {s : τ} (hs : s ∈ T) : Van T (X s : MvPowerSeries τ C) := by sorry
