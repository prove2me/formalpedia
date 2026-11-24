-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_aeval_inr
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.aeval_inr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:59:05.722852+00:00
-- url     : https://prove2.me/theorems/c2484a6c-99da-4671-81b2-453af3e364ab
-- title:
--   Exp Chart Jet A: aeval inr
-- statement:
--   The Exp Chart Jet A construction uses the aeval inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L37-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L37-L63

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.aeval_inr {κ : Type} [Fintype κ] [DecidableEq κ] (g : κ → R) (P : MvPolynomial κ R) :
    MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) P =
      TrivSqZeroExt.inl (MvPolynomial.coeff 0 P) +
        TrivSqZeroExt.inr (∑ q, g q * MvPolynomial.coeff (Finsupp.single q 1) P) := by sorry
