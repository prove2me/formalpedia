-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_split
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:42:00.813974+00:00
-- url     : https://prove2.me/theorems/270f97a2-4b54-4007-9351-d4410283c94d
-- title:
--   GL2 Prime Sums: gl2a5 split
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L274-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L274-L285

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_split (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (K N : ℕ) :
    ∑ n ∈ Icc 1 N, f n ≤ ∑ n ∈ Icc 1 K, f n + ∑ n ∈ Ioc K N, f n := by sorry
