-- Prove2me | Theorems.Thm_Formalism_SA_P_trace_pow_eq_sum
-- name    : Formalism.SA.P.trace_pow_eq_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:59.192087+00:00
-- url     : https://prove2.me/theorems/06c3c882-3256-4b99-9f85-bb32d172056a
-- title:
--   P: trace pow eq sum
-- statement:
--   The P construction uses the trace pow eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/PowFinrankEqZeroOfTracePow.lean#L91-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/PowFinrankEqZeroOfTracePow.lean#L91-L114

import Definitions.Def_Formalism_LatticeRigidity_StatementD
import Mathlib
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open Matrix Polynomial
open scoped ComplexOrder
variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem Formalism.SA.P.trace_pow_eq_sum (f : Module.End K V) (j : ℕ) :
    LinearMap.trace K V (f ^ j) = ∑ μ ∈ (finite_eig f).toFinset,
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by sorry
