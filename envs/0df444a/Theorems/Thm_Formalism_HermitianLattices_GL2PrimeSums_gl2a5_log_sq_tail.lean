-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_log_sq_tail
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_log_sq_tail
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:57.463802+00:00
-- url     : https://prove2.me/theorems/6d64a48a-b050-4b3d-9c05-7b2a1b9e4ce8
-- title:
--   GL2 Prime Sums: gl2a5 log sq tail
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 log sq tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L296-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L296-L329

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_log_sq_tail (K : ℕ) (hK : 1 ≤ K) (M : ℕ) :
    ∑ n ∈ Ioc K M, Real.log n / (n : ℝ) ^ 2 ≤ (Real.log K + 2) / (K : ℝ) := by sorry
