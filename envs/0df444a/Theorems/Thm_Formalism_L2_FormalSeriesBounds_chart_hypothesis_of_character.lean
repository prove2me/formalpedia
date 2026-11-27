-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_chart_hypothesis_of_character
-- name    : Formalism.L2.FormalSeriesBounds.chart_hypothesis_of_character
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T04:56:41.563051+00:00
-- url     : https://prove2.me/theorems/a469d8d3-90f1-45a2-86c1-700e8a7b552f
-- title:
--   Formal Series Bounds: chart hypothesis of character
-- statement:
--   The Formal Series Bounds construction uses the chart hypothesis of character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieChar.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieChar.lean#L94-L96

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieTop
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieChar
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]
open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

theorem Formalism.L2.FormalSeriesBounds.chart_hypothesis_of_character (hG : CharGermSt) (h : CharacterHypothesisCharts Xo c) : CharacterHypothesisAllCharts Xo c := by sorry
