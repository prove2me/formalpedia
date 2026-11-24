-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_le_log
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5s_le_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:03.492912+00:00
-- url     : https://prove2.me/theorems/dc532063-a468-4d1e-bc5c-af970caa9b38
-- title:
--   GL2 Prime Sums: gl2a5s le log
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5s le log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L468-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L468-L484

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5s_le_log {x : ℝ} (hx : Real.exp 1 ≤ x) (N p : ℕ) :
    primeTermWeight x N p ≤ 3 * Real.log x := by sorry
