-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_outPart_primePow
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_outPart_primePow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:19.44817+00:00
-- url     : https://prove2.me/theorems/88743d02-4904-4de6-b652-d39f8449300b
-- title:
--   GL2 Prime Sums: gl2a5 out Part prime Pow
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 out Part prime Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L8-L18

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_outPart_primePow (m₀ : ℕ) {n : ℕ} (hn : IsPrimePow n) :
    ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p ^ k ∧ n.minFac = p ∧
      outPart m₀ n = if (¬ p ∣ m₀ ∧ Odd k) then p else 1 := by sorry
