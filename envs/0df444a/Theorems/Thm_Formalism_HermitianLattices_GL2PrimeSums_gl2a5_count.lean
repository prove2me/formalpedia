-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_count
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:54.669057+00:00
-- url     : https://prove2.me/theorems/8bedfa2b-cb1b-4549-aaf8-6641c6fe61b6
-- title:
--   GL2 Prime Sums: gl2a5 count
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L486-L498
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L486-L498

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_count (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    ∑ p ∈ Icc 1 N, (if (p : ℝ) ≤ Y then (1 : ℝ) else 0) ≤ Y := by sorry
