-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2_coeff_linR
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.coeff_linR
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:59:31.74782+00:00
-- url     : https://prove2.me/theorems/5ccf0b19-50d4-4311-be5c-391b41f771ba
-- title:
--   CInd Fr Exp2: coeff lin R
-- statement:
--   The CInd Fr Exp2 construction uses the coeff lin R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupLinearSecond.lean#L449-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupLinearSecond.lean#L449-L464

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
variable {S : Type} [CommRing S] {d : ℕ}
variable [Algebra ℚ S]
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.coeff_linR (Ab B : Fin d → Fin d → S) (i0 l0 : Fin d) :
    coeff (sil i0 l0) (∑ i, ∑ l, C (B i l) * (xs S d (0 : Fin 2) i * PairEvaluation.lin Ab (1 : Fin 2) l)) =
      ∑ l, B i0 l * Ab l l0 := by sorry
