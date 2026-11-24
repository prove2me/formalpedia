-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_expand
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:53.994555+00:00
-- url     : https://prove2.me/theorems/ad4b6341-6b61-4b2a-8f28-979b0d56576a
-- title:
--   GL2 Prime Sums: gl2a5 expand
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L173-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L173-L210

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_expand (I PPs : Finset ℕ) (a : ℕ → ℂ) (c : ℕ → ℝ) (ha : ∀ n, ‖a n‖ ≤ c n) :
    ∑ q ∈ PPs, ‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)| := by sorry
