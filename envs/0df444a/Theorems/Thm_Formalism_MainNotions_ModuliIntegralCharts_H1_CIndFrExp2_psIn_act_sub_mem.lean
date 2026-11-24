-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2_psIn_act_sub_mem
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.psIn_act_sub_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:58:43.728817+00:00
-- url     : https://prove2.me/theorems/765bd096-6845-4dff-aeee-06d4fd3a06e1
-- title:
--   CInd Fr Exp2: ps In act sub mem
-- statement:
--   The CInd Fr Exp2 construction uses the ps In act sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupLinearSecond.lean#L499-L532
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupLinearSecond.lean#L499-L532

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
open ReciprocityTheory.ChartRestriction.G.TB (dLin)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.psIn_act_sub_mem (φ : Fin d → PS S 1 d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {m : ℕ}
    (hm : 1 ≤ m) (k : Fin 2) (i : Fin d) :
    psIn d m ![k] (φ i) - C (constantCoeff (psIn d m ![k] (φ i))) - PairEvaluation.lin (dLin φ) k i ∈
      Io S (Fin 2 × Fin d) ^ 2 := by sorry
