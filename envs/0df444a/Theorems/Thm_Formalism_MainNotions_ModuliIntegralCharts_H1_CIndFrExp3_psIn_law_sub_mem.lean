-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp3_psIn_law_sub_mem
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3.psIn_law_sub_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:12:45.570333+00:00
-- url     : https://prove2.me/theorems/53e0ba74-2482-458a-b11d-339166168b6b
-- title:
--   CInd Fr Exp3: ps In law sub mem
-- statement:
--   The CInd Fr Exp3 construction uses the ps In law sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/IsUnitCoeffZero.lean#L67-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/IsUnitCoeffZero.lean#L67-L81

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BalOf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IsUnitCoeffZero
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
variable {S : Type} [CommRing S] {d : ℕ}
variable [Algebra ℚ S]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3.psIn_law_sub_mem (G : FGLaw S d) {m : ℕ} (hm : 1 ≤ m) (i : Fin d) :
    psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F i) - C (constantCoeff (psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F i))) - (xs S d 0 i + xs S d 1 i) ∈
      Io S (Fin 3 × Fin d) ^ 2 := by sorry
