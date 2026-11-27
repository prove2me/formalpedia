-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_const_cvAt
-- name    : Formalism.L2.FormalSeriesBounds.const_cvAt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:47.591022+00:00
-- url     : https://prove2.me/theorems/42f0b38e-0395-5c75-8c6b-8a1c43ade362
-- title:
--   Formal Series Bounds: const cv At
-- statement:
--   The Formal Series Bounds construction uses the const cv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L129-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L129-L131

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
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.const_cvAt {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {γ : PowerSeries C}
    (hγ : PowerSeries.constantCoeff γ = 0) : MvPowerSeries.constantCoeff (cvAt s γ) = 0 := by sorry
