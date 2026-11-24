-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_monomial_mem_orig_pow
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.monomial_mem_orig_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:01:18.685123+00:00
-- url     : https://prove2.me/theorems/20a1ba0e-b3ae-44e4-a99b-bb8cbe194728
-- title:
--   Gauge R: monomial mem orig pow
-- statement:
--   The Gauge R construction uses the monomial mem orig pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L15-L23

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.monomial_mem_orig_pow (e : ι →₀ ℕ) (a : R) : monomial e a ∈ orig R ι ^ e.degree := by sorry
