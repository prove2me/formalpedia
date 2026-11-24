-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_expS_add
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.expS_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:02:36.016508+00:00
-- url     : https://prove2.me/theorems/144c6db3-305c-45ed-8058-50063fbc846c
-- title:
--   Partial Derivative Exponent: exp S add
-- statement:
--   The Partial Derivative Exponent construction uses the exp S add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L252-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L252-L261

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.expS_add {τ : Type} (x y : MvPowerSeries τ k) (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) :
    PowerSeries.subst (x + y) (PowerSeries.exp k) =
      PowerSeries.subst x (PowerSeries.exp k) * PowerSeries.subst y (PowerSeries.exp k) := by sorry
