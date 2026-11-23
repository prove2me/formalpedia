-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_abel
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_abel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:20:25.766806+00:00
-- url     : https://prove2.me/theorems/6c6f6818-1032-4159-bf70-6d3fdf4d7256
-- title:
--   GL2 Prime Sums: gl2a5 abel
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 abel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L212-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L212-L250

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_abel (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (g : ℕ → ℝ) (K : ℕ)
    (hanti : ∀ n, K < n → g (n + 1) ≤ g n) (hnn : ∀ n, K < n → 0 ≤ g n) (M : ℕ) :
    ∑ n ∈ Ioc K M, Λ n * g n ≤ 2 * ((K : ℝ) + 1) * g (K + 1) + 2 * ∑ n ∈ Ioc (K + 1) M, g n := by sorry
