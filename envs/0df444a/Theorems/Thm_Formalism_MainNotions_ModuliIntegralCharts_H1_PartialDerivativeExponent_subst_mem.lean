-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_subst_mem
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.subst_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:02:31.435644+00:00
-- url     : https://prove2.me/theorems/3f520fa6-d34a-437a-bb44-22476342cf7f
-- title:
--   Partial Derivative Exponent: subst mem
-- statement:
--   The Partial Derivative Exponent construction uses the subst mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L69-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L69-L82

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.subst_mem {τ : Type} {V : Set σ} (a : τ → MvPowerSeries σ k) (ha : HasSubst a)
    (haV : ∀ t, a t ∈ subV k V) (f : MvPowerSeries τ k) : subst a f ∈ subV k V := by sorry
