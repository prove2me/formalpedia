-- Prove2me | Theorems.Thm_Formalism_L2_Pj_wtField_of_borChart
-- name    : Formalism.L2.Pj.wtField_of_borChart
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:58.456973+00:00
-- url     : https://prove2.me/theorems/a3d0ac3e-4837-48e4-b0ac-6f16c584e92e
-- title:
--   Pj: wt Field of bor Chart
-- statement:
--   The Pj construction uses the wt Field of bor Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnitIndepOfCharts.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnitIndepOfCharts.lean#L32-L34

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartWD
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem Formalism.L2.Pj.wtField_of_borChart (h : BorChartF Xo c) : WtField Xo c := by sorry
