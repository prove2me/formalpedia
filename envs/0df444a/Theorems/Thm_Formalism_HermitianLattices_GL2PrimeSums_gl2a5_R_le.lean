-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_R_le
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_R_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:50.955108+00:00
-- url     : https://prove2.me/theorems/f3231cc5-1e3b-4925-ae15-43b3f57712f6
-- title:
--   GL2 Prime Sums: gl2a5 R le
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 R le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L764-L789
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L764-L789

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_R_le (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) {x : ℝ}
    (hx : Real.exp 1 ≤ x) (N m₀ : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (h : ∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ N → (p : ℝ) ≤ Y) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n ≤
      Y * (3 * Real.log x) + 6 * Real.sqrt x := by sorry
