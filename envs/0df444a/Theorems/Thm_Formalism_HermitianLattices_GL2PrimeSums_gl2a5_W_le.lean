-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_W_le
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_W_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:28.574035+00:00
-- url     : https://prove2.me/theorems/2662573d-5b00-4d51-b846-da1cb8cc2178
-- title:
--   GL2 Prime Sums: gl2a5 W le
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 W le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L813-L832
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L813-L832

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_W_le {x : ℝ} (hx : 0 ≤ x) (N m₀ d : ℕ) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = d), cn x n ≤
      ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n + primeTermWeight x N d := by sorry
