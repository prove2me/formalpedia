-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_cc_logOf
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a.cc_logOf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:58:06.907783+00:00
-- url     : https://prove2.me/theorems/0858be1c-142b-41f3-9d11-8696ff7993ff
-- title:
--   CInd Fr Exp2a: cc log Of
-- statement:
--   The CInd Fr Exp2a construction uses the cc log Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LogLowOrderOne.lean#L173-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LogLowOrderOne.lean#L173-L176

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.FG.SolveVAux Formalism.L2.Pj
variable {S : Type} [CommRing S]
variable [Algebra ℚ S] {d : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a.cc_logOf (G : FGLaw S d) (i : Fin d) : constantCoeff (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = 0 := by sorry
