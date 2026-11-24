-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_aeval_scale_monomial
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.aeval_scale_monomial
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:01:59.113801+00:00
-- url     : https://prove2.me/theorems/52eda87f-252f-4413-820e-323c95bf50b5
-- title:
--   Gauge R: aeval scale monomial
-- statement:
--   The Gauge R construction uses the aeval scale monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L67-L73

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPolynomial Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
variable {R ι : Type} [CommRing R]
variable [Fintype ι] [DecidableEq ι]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.aeval_scale_monomial (s : ι → R) (e : ι →₀ ℕ) (a : R) :
    aeval (fun i => C (s i) * X i) (monomial e a : MvPolynomial ι R) =
      monomial e (a * e.prod fun i k => s i ^ k) := by sorry
