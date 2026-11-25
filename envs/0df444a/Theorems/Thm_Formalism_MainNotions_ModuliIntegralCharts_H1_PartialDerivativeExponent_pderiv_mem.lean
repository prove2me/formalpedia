-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_pderiv_mem
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.pderiv_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:03:07.421879+00:00
-- url     : https://prove2.me/theorems/6409531d-c3e8-440f-9e50-22371bda5d9b
-- title:
--   Partial Derivative Exponent: pderiv mem
-- statement:
--   The Partial Derivative Exponent construction uses the pderiv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L84-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L84-L93

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
open MvPowerSeries
variable {σ : Type}
variable {k : Type} [CommRing k]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.pderiv_mem {V : Set σ} (i : σ) {f : MvPowerSeries σ k} (hf : f ∈ subV k V) :
    pderiv k i f ∈ subV k V := by sorry
