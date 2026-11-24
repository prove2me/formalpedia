-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_inv_sq_tail
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_inv_sq_tail
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:14.953423+00:00
-- url     : https://prove2.me/theorems/0a13b8f1-69f1-481e-b765-103f2aa0c621
-- title:
--   GL2 Prime Sums: gl2a5 inv sq tail
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 inv sq tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L287-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L287-L294

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_inv_sq_tail (K : ℕ) (hK : 1 ≤ K) (M : ℕ) :
    ∑ n ∈ Ioc K M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by sorry
