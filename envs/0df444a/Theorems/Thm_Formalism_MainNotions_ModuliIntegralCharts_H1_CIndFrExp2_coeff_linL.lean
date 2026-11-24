-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2_coeff_linL
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.coeff_linL
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:58:46.62091+00:00
-- url     : https://prove2.me/theorems/15ab952b-6907-4aba-8553-eeb3c661465e
-- title:
--   CInd Fr Exp2: coeff lin L
-- statement:
--   The CInd Fr Exp2 construction uses the coeff lin L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupLinearSecond.lean#L432-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupLinearSecond.lean#L432-L447

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.coeff_linL (A B : Fin d → Fin d → S) (i0 l0 : Fin d) :
    coeff (sil i0 l0) (∑ i, ∑ l, C (B i l) * (PairEvaluation.lin A (0 : Fin 2) i * xs S d (1 : Fin 2) l)) =
      ∑ i, A i i0 * B i l0 := by sorry
