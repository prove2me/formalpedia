-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_mem_subV
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.mem_subV
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:07.128795+00:00
-- url     : https://prove2.me/theorems/58142f6b-914c-4030-ba07-3ac593d1ac4f
-- title:
--   Partial Derivative Exponent: mem sub V
-- statement:
--   The Partial Derivative Exponent construction uses the mem sub V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L57-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean#L57-L57

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.mem_subV (V : Set σ) (f : MvPowerSeries σ k) : f ∈ subV k V ↔ OnV V f := by sorry
