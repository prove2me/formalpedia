-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2_jetSubstP_mk
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.jetSubstP_mk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:58:20.9596+00:00
-- url     : https://prove2.me/theorems/03f079eb-c3ce-4552-8f02-db9cc3087791
-- title:
--   CInd Fr Exp2: jet Subst P mk
-- statement:
--   The CInd Fr Exp2 construction uses the jet Subst P mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupLinearSecond.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupLinearSecond.lean#L17-L19

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.jetSubstP_mk {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (P : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (aeval (fun i => φ i - C (constantCoeff (φ i))) P) := by sorry
