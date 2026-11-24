-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_fiber_le
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_fiber_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:07.373003+00:00
-- url     : https://prove2.me/theorems/79a69066-3aa2-4191-88f3-3bcef0e8e46d
-- title:
--   GL2 Prime Sums: gl2a5 fiber le
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 fiber le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L347-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L347-L379

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_fiber_le (N p : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac = p), f n ≤ ∑ a ∈ Icc 1 N, f (p ^ a) := by sorry
