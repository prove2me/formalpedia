-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_sum_ind
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_sum_ind
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:06.305945+00:00
-- url     : https://prove2.me/theorems/ff77ff50-038d-44d2-88ab-fc4bf00d75b1
-- title:
--   GL2 Prime Sums: gl2a5 sum ind
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 sum ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L130-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L130-L136

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_sum_ind (P : Finset ℕ) (c : ℕ → ℝ) (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B] :
    ∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if A n ∧ B n' then (1 : ℝ) else 0) =
      (∑ n ∈ P.filter A, c n) * (∑ n ∈ P.filter B, c n) := by sorry
