-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_sq_sum_fin
-- name    : Formalism.HermitianLatticeCounting.P.sq_sum_fin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:00.179805+00:00
-- url     : https://prove2.me/theorems/4aa2c7c3-8561-4746-beb7-e8d68dd9a5a7
-- title:
--   P: sq sum fin
-- statement:
--   The P construction uses the sq sum fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CoefficientLeOperatorNorm.lean#L1147-L1171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CoefficientLeOperatorNorm.lean#L1147-L1171

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.sq_sum_fin {a : ℕ} (j : Fin a → ℕ) :
    (∑ x, j x) ^ 2 = (∑ x, j x ^ 2)
      + 2 * ∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y := by sorry
