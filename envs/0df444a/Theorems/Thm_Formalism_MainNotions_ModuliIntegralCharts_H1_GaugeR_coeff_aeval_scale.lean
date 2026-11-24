-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_coeff_aeval_scale
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.coeff_aeval_scale
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:02:15.991803+00:00
-- url     : https://prove2.me/theorems/88a9441d-b769-4d13-9530-8e84107889b7
-- title:
--   Gauge R: coeff aeval scale
-- statement:
--   The Gauge R construction uses the coeff aeval scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L75-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L75-L85

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.coeff_aeval_scale (s : ι → R) (p : MvPolynomial ι R) (e : ι →₀ ℕ) :
    coeff e (aeval (fun i => C (s i) * X i) p) = (e.prod fun i k => s i ^ k) * coeff e p := by sorry
