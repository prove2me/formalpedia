-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_cn_nonneg
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_cn_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:42:09.367484+00:00
-- url     : https://prove2.me/theorems/45f207d9-42f8-49ec-b79b-a1a03151b72c
-- title:
--   GL2 Prime Sums: gl2a5 cn nonneg
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 cn nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L331-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L331-L333

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_cn_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ cn x n := by sorry
