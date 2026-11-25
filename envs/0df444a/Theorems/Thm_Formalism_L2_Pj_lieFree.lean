-- Prove2me | Theorems.Thm_Formalism_L2_Pj_lieFree
-- name    : Formalism.L2.Pj.lieFree
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:02:30.656443+00:00
-- url     : https://prove2.me/theorems/522bf700-cb36-49b7-847d-e10b91f5975b
-- title:
--   Pj: lie Free
-- statement:
--   The Pj construction uses the lie Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieFreePf.lean#L38-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieFreePf.lean#L38-L156

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntFrames
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieAlg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieRel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieFreePf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanBC_alg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_tmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_univChartLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj tvec_eig_iff isTan_tvec tcoord tcoord_spec univChartLoc tanBC_alg
  pushR pushR_left pushR_inj pushR_map tvec_tmap fB scaleD IsUnivChart dualMapA)
open Formalism.L2.Pj.LieRel Formalism.L2.Pj.LieAlg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
set_option maxHeartbeats 800000

theorem Formalism.L2.Pj.lieFree : LieFreeSt Xo c := by sorry
