-- Prove2me | Theorems.Thm_Formalism_L2_DIV_trace_isIntegral_of_pow_eq_one
-- name    : Formalism.L2.DIV.trace_isIntegral_of_pow_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:11.439801+00:00
-- url     : https://prove2.me/theorems/e03bf1a7-f4a4-445f-9c3b-ae3205f8f601
-- title:
--   DIV: trace is Integral of pow eq one
-- statement:
--   The DIV construction uses the trace is Integral of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L588-L602
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L588-L602

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues

theorem Formalism.L2.DIV.trace_isIntegral_of_pow_eq_one {k V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (f : Module.End k V) {N : ℕ} (hN : N ≠ 0) (hf : f ^ N = 1) :
    IsIntegral ℤ (LinearMap.trace k V f) := by sorry
