-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_mem_orig_pow_of_coeff
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.mem_orig_pow_of_coeff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:01:28.629057+00:00
-- url     : https://prove2.me/theorems/801291fc-84d7-4cde-8a46-10deb7a822d8
-- title:
--   Gauge R: mem orig pow of coeff
-- statement:
--   The Gauge R construction uses the mem orig pow of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L25-L33

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.mem_orig_pow_of_coeff (n : ℕ) (p : MvPolynomial ι R) (h : ∀ e, e.degree < n → coeff e p = 0) :
    p ∈ orig R ι ^ n := by sorry
