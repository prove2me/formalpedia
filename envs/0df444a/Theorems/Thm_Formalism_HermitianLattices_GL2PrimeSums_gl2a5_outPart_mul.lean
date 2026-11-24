-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_outPart_mul
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_outPart_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:36.529278+00:00
-- url     : https://prove2.me/theorems/452ea5ef-5a7a-4013-9f23-789012e99990
-- title:
--   GL2 Prime Sums: gl2a5 out Part mul
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 out Part mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L20-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L20-L53

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_outPart_mul (m₀ : ℕ) {m m' : ℕ} (h : Nat.Coprime m m') :
    outPart m₀ (m * m') = outPart m₀ m * outPart m₀ m' := by sorry
