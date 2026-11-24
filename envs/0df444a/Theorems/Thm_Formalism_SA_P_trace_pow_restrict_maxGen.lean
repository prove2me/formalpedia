-- Prove2me | Theorems.Thm_Formalism_SA_P_trace_pow_restrict_maxGen
-- name    : Formalism.SA.P.trace_pow_restrict_maxGen
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:57.424804+00:00
-- url     : https://prove2.me/theorems/4cc3321d-e87f-4e8c-bc64-d7f59339ed46
-- title:
--   P: trace pow restrict max Gen
-- statement:
--   The P construction uses the trace pow restrict max Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/PowFinrankEqZeroOfTracePow.lean#L27-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/PowFinrankEqZeroOfTracePow.lean#L27-L89

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

theorem Formalism.SA.P.trace_pow_restrict_maxGen (f : Module.End K V) (μ : K) (j : ℕ) :
    LinearMap.trace K _ ((f ^ j).restrict
        (Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ)) =
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by sorry
