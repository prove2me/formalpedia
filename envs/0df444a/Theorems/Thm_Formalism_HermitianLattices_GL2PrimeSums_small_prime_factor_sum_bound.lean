-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_small_prime_factor_sum_bound
-- name    : Formalism.HermitianLattices.GL2PrimeSums.small_prime_factor_sum_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:16.161528+00:00
-- url     : https://prove2.me/theorems/5cc61731-12e7-484a-bead-2fba41d81b84
-- title:
--   GL2 Prime Sums: small prime factor sum bound
-- statement:
--   The GL2 Prime Sums construction uses the small prime factor sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L658-L686
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L658-L686

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

theorem Formalism.HermitianLattices.GL2PrimeSums.small_prime_factor_sum_bound {x : ℝ} (hx : Real.exp 1 ≤ x) (N m₀ : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (h : ∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ N → (p : ℝ) ≤ Y) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac ∣ m₀), cn x n ≤ Y * (3 * Real.log x) := by sorry
