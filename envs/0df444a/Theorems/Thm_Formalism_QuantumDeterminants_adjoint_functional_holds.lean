-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_adjoint_functional_holds
-- name    : Formalism.QuantumDeterminants.adjoint_functional_holds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:44.806715+00:00
-- url     : https://prove2.me/theorems/052b9e12-641d-46f3-9391-7e07de35b3d7
-- title:
--   Quantum Determinants: adjoint functional holds
-- statement:
--   The Quantum Determinants construction uses the adjoint functional holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L128-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L128-L225

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
variable {m : ℕ}

theorem Formalism.QuantumDeterminants.adjoint_functional_holds : AdjFun := by sorry
