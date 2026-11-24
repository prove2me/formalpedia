-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_cn_zero
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_cn_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:54.217915+00:00
-- url     : https://prove2.me/theorems/955ae5cd-5521-43d8-ac11-86e9cee56135
-- title:
--   GL2 Prime Sums: gl2a5 cn zero
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 cn zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L339-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L339-L341

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_cn_zero (x : ℝ) {n : ℕ} (hn : ¬ IsPrimePow n) : cn x n = 0 := by sorry
