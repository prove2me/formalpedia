-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_chart_log_constantCoeff
-- name    : Formalism.L2.FormalSeriesBounds.FBChart.chart_log_constantCoeff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:50.771922+00:00
-- url     : https://prove2.me/theorems/abfb536c-2afb-4f81-b902-3152f8a303c4
-- title:
--   FBChart: chart log constant Coeff
-- statement:
--   The FBChart construction uses the chart log constant Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L125-L129

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

theorem Formalism.L2.FormalSeriesBounds.FBChart.chart_log_constantCoeff (i : Fin dd) : MvPowerSeries.constantCoeff ((Y.raw p).lg i) = 0 := by sorry
