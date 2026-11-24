-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_diag_small
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_diag_small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:11.068654+00:00
-- url     : https://prove2.me/theorems/38d28625-8afb-4017-9bdb-2e959d11e468
-- title:
--   GL2 Prime Sums: gl2a5 diag small
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 diag small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L533-L575
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L533-L575

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_diag_small (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) {x : ℝ}
    (hx : Real.exp 1 ≤ x) (N : ℕ) :
    ∑ p ∈ Icc 1 ⌊x⌋₊, (primeTermWeight x N p) ^ 2 ≤ 30 * x * Real.log x := by sorry
