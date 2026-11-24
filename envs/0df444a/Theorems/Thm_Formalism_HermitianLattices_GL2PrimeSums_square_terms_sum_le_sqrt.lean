-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_square_terms_sum_le_sqrt
-- name    : Formalism.HermitianLattices.GL2PrimeSums.square_terms_sum_le_sqrt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:57.503984+00:00
-- url     : https://prove2.me/theorems/4f912f1e-2412-4705-84ea-dfc8d773b551
-- title:
--   GL2 Prime Sums: square terms sum le sqrt
-- statement:
--   The GL2 Prime Sums construction uses the square terms sum le sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L688-L762
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L688-L762

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

theorem Formalism.HermitianLattices.GL2PrimeSums.square_terms_sum_le_sqrt (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => IsSquare n), cn x n ≤ 6 * Real.sqrt x := by sorry
