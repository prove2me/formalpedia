-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2b_ev_bilL
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b.ev_bilL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:28:33.467104+00:00
-- url     : https://prove2.me/theorems/9afb4fab-e6fb-49b2-b9a4-1260a159b383
-- title:
--   CInd Fr Fix2b: ev bil L
-- statement:
--   The CInd Fr Fix2b construction uses the ev bil L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffAddSecondThird.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffAddSecondThird.lean#L48-L55

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b.ev_bilL {n : ℕ} (G : FGLaw S d) (cc : Fin d → Fin d → S) (a : Fin 2 → Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) :
    ev a (bilL G cc) = ∑ i, ∑ l, cc i l • (ev ![a 0] (LogPf.logOf G i) * ev ![a 1] (LogPf.logOf G l)) := by sorry
