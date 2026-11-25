-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_sum
-- name    : Formalism.L2.FormalSeriesBounds.van_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:03.197557+00:00
-- url     : https://prove2.me/theorems/02c6d76f-0b6e-46a3-8f6b-f1abb915ebee
-- title:
--   Formal Series Bounds: van sum
-- statement:
--   The Formal Series Bounds construction uses the van sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePAxesSelfSt.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePAxesSelfSt.lean#L15-L19

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
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

theorem Formalism.L2.FormalSeriesBounds.van_sum {τ ι : Type} {T : Set τ} (s : Finset ι) (f : ι → MvPowerSeries τ C) (hf : ∀ i ∈ s, Van T (f i)) :
    Van T (∑ i ∈ s, f i) := by sorry
