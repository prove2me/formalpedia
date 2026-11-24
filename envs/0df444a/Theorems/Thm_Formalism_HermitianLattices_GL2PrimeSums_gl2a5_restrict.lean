-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_restrict
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_restrict
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:14.928064+00:00
-- url     : https://prove2.me/theorems/a25220b7-9d38-4ab7-b654-7ab9caeaeb85
-- title:
--   GL2 Prime Sums: gl2a5 restrict
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L791-L798
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L791-L798

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_restrict (x : ℝ) (N : ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, cn x n * F n = ∑ n ∈ primesLeFinset N, cn x n * F n := by sorry
