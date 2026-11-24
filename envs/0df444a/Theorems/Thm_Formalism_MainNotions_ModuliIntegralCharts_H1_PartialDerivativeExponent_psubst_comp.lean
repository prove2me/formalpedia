-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_psubst_comp
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.psubst_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:02:42.556873+00:00
-- url     : https://prove2.me/theorems/ec741b7a-26b4-406e-bb77-da02b6211a2f
-- title:
--   Partial Derivative Exponent: psubst comp
-- statement:
--   The Partial Derivative Exponent construction uses the psubst comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L245-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L245-L250

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.psubst_comp {τ υ : Type} (b : τ → MvPowerSeries υ k) (hb : HasSubst b)
    (a : MvPowerSeries τ k) (ha : constantCoeff a = 0) (f : PowerSeries k) :
    subst b (PowerSeries.subst a f) = PowerSeries.subst (subst b a) f := by sorry
