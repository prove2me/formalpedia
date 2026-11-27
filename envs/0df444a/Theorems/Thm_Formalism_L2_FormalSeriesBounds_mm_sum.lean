-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_mm_sum
-- name    : Formalism.L2.FormalSeriesBounds.mm_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:07:41.387785+00:00
-- url     : https://prove2.me/theorems/e19ba6ab-0a2a-5974-a930-c400ed281782
-- title:
--   Formal Series Bounds: mm sum
-- statement:
--   The Formal Series Bounds construction uses the mm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L111-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L111-L118

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] {V : VF C}

theorem Formalism.L2.FormalSeriesBounds.mm_sum {ι : Type} (s : Finset ι) (f : ι → C) (hf : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by sorry
