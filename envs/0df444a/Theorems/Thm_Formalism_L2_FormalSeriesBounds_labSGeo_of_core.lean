-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_labSGeo_of_core
-- name    : Formalism.L2.FormalSeriesBounds.labSGeo_of_core
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:11:39.814388+00:00
-- url     : https://prove2.me/theorems/22eed547-dc02-4a9f-96de-d60f1dffb3ab
-- title:
--   Formal Series Bounds: lab SGeo of core
-- statement:
--   The Formal Series Bounds construction uses the lab SGeo of core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieSelfCuts.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieSelfCuts.lean#L62-L64

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieLab
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCH
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelfCuts
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
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (Xo c)

theorem Formalism.L2.FormalSeriesBounds.labSGeo_of_core (h : LabSGeoCoreSt Xo c) : LabSGeoSt Xo c := by sorry
