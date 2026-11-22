-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_nonneg
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5s_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:11.97532+00:00
-- url     : https://prove2.me/theorems/c3ec2805-db4d-4392-b431-d9923eb1d189
-- title:
--   GL2 Prime Sums: gl2a5s nonneg
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5s nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L381-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L381-L382

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5s_nonneg {x : ℝ} (hx : 0 ≤ x) (N p : ℕ) : 0 ≤ primeTermWeight x N p := by sorry
