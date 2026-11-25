-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_pderiv_kill
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.pderiv_kill
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:45.458518+00:00
-- url     : https://prove2.me/theorems/af8d8182-47a6-4c6a-a5de-b9bbf1284e2b
-- title:
--   Partial Derivative Exponent: pderiv kill
-- statement:
--   The Partial Derivative Exponent construction uses the pderiv kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L95-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L95-L106

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.pderiv_kill {V : Set σ} {i : σ} (hi : i ∉ V) {f : MvPowerSeries σ k} (hf : f ∈ subV k V) :
    pderiv k i f = 0 := by sorry
