-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rank_maximal_charts_of_nondegenerate
-- name    : Formalism.L2.FormalSeriesBounds.rank_maximal_charts_of_nondegenerate
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:19.227676+00:00
-- url     : https://prove2.me/theorems/b332e5a6-3ddf-4113-bc1d-2c130cfef102
-- title:
--   Formal Series Bounds: rank maximal charts of nondegenerate
-- statement:
--   The Formal Series Bounds construction uses the rank maximal charts of nondegenerate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NondegenerateCharts.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NondegenerateCharts.lean#L52-L54

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieTop
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2

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
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

theorem Formalism.L2.FormalSeriesBounds.rank_maximal_charts_of_nondegenerate (h1 : RankMaximalOfNondegenerate) (h2 : NondegenerateCharts Xo c) : RankMaximalCharts Xo c := by sorry
