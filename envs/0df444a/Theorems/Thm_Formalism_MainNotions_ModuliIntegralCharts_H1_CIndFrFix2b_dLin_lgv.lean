-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2b_dLin_lgv
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b.dLin_lgv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:36:53.047073+00:00
-- url     : https://prove2.me/theorems/a1d29ded-ed1d-4032-b2ee-c373d6126838
-- title:
--   CInd Fr Fix2b: d Lin lgv
-- statement:
--   The CInd Fr Fix2b construction uses the d Lin lgv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffAddSecondThird.lean#L270-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffAddSecondThird.lean#L270-L277

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HomUniq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddSecondThird
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_hasSubst_pts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b.dLin_lgv (G : FGLaw S d) : dLin (lgv G) = 1 := by sorry
