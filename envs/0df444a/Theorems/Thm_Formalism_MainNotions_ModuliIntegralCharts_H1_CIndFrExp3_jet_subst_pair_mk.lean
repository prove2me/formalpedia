-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp3_jet_subst_pair_mk
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3.jet_subst_pair_mk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:11:41.165223+00:00
-- url     : https://prove2.me/theorems/298982c1-22f4-4653-b5ef-243d7b7b4f79
-- title:
--   CInd Fr Exp3: jet subst pair mk
-- statement:
--   The CInd Fr Exp3 construction uses the jet subst pair mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/IsUnitCoeffZero.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/IsUnitCoeffZero.lean#L19-L32

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3.jet_subst_pair_mk {κ' : Type} (m : ℕ) (u v : Fin d → MvPolynomial κ' S) (P : MvPolynomial (Fin 2 × Fin d) S) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![u, v] : Fin 2 → Fin d → MvPolynomial κ' S) p.1 p.2)
        (Ideal.Quotient.mk (orig S (Fin 2 × Fin d) ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1))
        (ev2 P (fun j => u j - C (constantCoeff (u j))) (fun j => v j - C (constantCoeff (v j)))) := by sorry
