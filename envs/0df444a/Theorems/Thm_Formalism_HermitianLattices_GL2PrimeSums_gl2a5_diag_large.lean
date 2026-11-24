-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_diag_large
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_diag_large
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:05.9038+00:00
-- url     : https://prove2.me/theorems/9a5e5f77-aff7-476a-9c71-c57fe479fef9
-- title:
--   GL2 Prime Sums: gl2a5 diag large
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 diag large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L598-L647
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L598-L647

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_diag_large (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) {x : ℝ}
    (hx : 3 ≤ x) (N : ℕ) :
    ∑ p ∈ Ioc ⌊x⌋₊ N, (primeTermWeight x N p) ^ 2 ≤ 32 * x * Real.log x := by sorry
