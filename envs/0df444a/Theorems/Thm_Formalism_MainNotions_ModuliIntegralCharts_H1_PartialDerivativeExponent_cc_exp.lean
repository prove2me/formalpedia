-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_cc_exp
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.cc_exp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:02:52.279727+00:00
-- url     : https://prove2.me/theorems/b3162d40-b0ff-4ba8-ade1-22e31823b0cc
-- title:
--   Partial Derivative Exponent: cc exp
-- statement:
--   The Partial Derivative Exponent construction uses the cc exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L263-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L263-L269

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
variable [Algebra ℚ k]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.cc_exp {τ : Type} (x : MvPowerSeries τ k) (hx : constantCoeff x = 0) :
    constantCoeff (PowerSeries.subst x (PowerSeries.exp k)) = 1 := by sorry
