-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_exp_biv
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.exp_biv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:02:21.432935+00:00
-- url     : https://prove2.me/theorems/ab1d4185-f11b-4b34-be7b-4edbc8f25367
-- title:
--   Partial Derivative Exponent: exp biv
-- statement:
--   The Partial Derivative Exponent construction uses the exp biv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L176-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L176-L243

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.exp_biv :
    PowerSeries.subst (X (0 : Fin 2) + X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) =
      PowerSeries.subst (X (0 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) := by sorry
