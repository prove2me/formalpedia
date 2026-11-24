-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_pointwise
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_pointwise
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:16.8029+00:00
-- url     : https://prove2.me/theorems/2e44467c-f2f4-4776-8d23-f9936dfa9ad2
-- title:
--   GL2 Prime Sums: gl2a5 pointwise
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 pointwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L82-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L82-L128

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_pointwise (m₀ nStar : ℕ) {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n')
    (μ δ : ℝ) (hδ : 0 ≤ δ) (hμ1 : |μ| ≤ 1)
    (hμ : outPart m₀ (n * n') ≠ 1 → outPart m₀ (n * n') ≠ nStar → |μ| ≤ δ) :
    |μ| ≤ δ + (if n.minFac = n'.minFac then (1 : ℝ) else 0)
      + (if outPart m₀ n = 1 ∧ outPart m₀ n' = 1 then (1 : ℝ) else 0)
      + (if outPart m₀ n = nStar.minFac ∧ outPart m₀ n' = nStar / nStar.minFac then (1 : ℝ) else 0)
      + (if outPart m₀ n = nStar / nStar.minFac ∧ outPart m₀ n' = nStar.minFac then (1 : ℝ) else 0) := by sorry
