-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp3_X_sub_cc
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3.X_sub_cc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:10:53.285664+00:00
-- url     : https://prove2.me/theorems/2e480563-85de-49e0-b2c8-0dc18c7af5f3
-- title:
--   CInd Fr Exp3: X sub cc
-- statement:
--   The CInd Fr Exp3 construction uses the X sub cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/IsUnitCoeffZero.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/IsUnitCoeffZero.lean#L34-L38

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3.X_sub_cc {n : ℕ} (k : Fin n) :
    (fun j => (X (k, j) : MvPolynomial (Fin n × Fin d) S) - C (constantCoeff (X (k, j) : MvPolynomial (Fin n × Fin d) S))) =
      xs S d k := by sorry
