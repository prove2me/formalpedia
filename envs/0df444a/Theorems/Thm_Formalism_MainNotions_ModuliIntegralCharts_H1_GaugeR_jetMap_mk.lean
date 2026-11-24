-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_jetMap_mk
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.jetMap_mk
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:48.121033+00:00
-- url     : https://prove2.me/theorems/b0ca21d6-2d7d-452f-b653-1477274c1a85
-- title:
--   Gauge R: jet Map mk
-- statement:
--   The Gauge R construction uses the jet Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L87-L89

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.jetMap_mk {ι' : Type} (m : ℕ) (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι')
    (p : MvPolynomial ι R) :
    jetMap φ hφ (Ideal.Quotient.mk (orig R ι ^ (m + 1)) p) = Ideal.Quotient.mk _ (aeval φ p) := by sorry
