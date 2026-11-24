-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_diag_eq
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_diag_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:23.054804+00:00
-- url     : https://prove2.me/theorems/796ade1d-9a8b-422c-99dd-94e5af8d9e2f
-- title:
--   GL2 Prime Sums: gl2a5 diag eq
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 diag eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L505-L525
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L505-L525

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_diag_eq (x : ℝ) (N : ℕ) :
    ∑ n ∈ primesLeFinset N, ∑ n' ∈ primesLeFinset N, cn x n * cn x n' *
      (if n.minFac = n'.minFac then (1 : ℝ) else 0) = ∑ p ∈ Icc 1 N, (primeTermWeight x N p) ^ 2 := by sorry
