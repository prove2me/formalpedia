-- Prove2me | Theorems.Thm_Formalism_L2_Pj_exist3_of
-- name    : Formalism.L2.Pj.exist3_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:46.386869+00:00
-- url     : https://prove2.me/theorems/b77c8eb5-164a-466b-9421-460ff5f2e497
-- title:
--   Pj: exist3 of
-- statement:
--   The Pj construction uses the exist3 of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnitIndepOfCharts.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnitIndepOfCharts.lean#L39-L41

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

theorem Formalism.L2.Pj.exist3_of (hC : FrChartF Xo c) (hB : BorChartF Xo c) (hL : IntLatU Xo c) :
    EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ∧ WtField Xo c ∧ IntDiagUnit Xo c := by sorry
