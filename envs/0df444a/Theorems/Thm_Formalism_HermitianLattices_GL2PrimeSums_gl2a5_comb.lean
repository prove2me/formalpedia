-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_comb
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_comb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:52.536187+00:00
-- url     : https://prove2.me/theorems/e5e14bdb-9bae-4f15-b1d1-b386c3ae38d9
-- title:
--   GL2 Prime Sums: gl2a5 comb
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L138-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L138-L171

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_comb (P : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (o mf : ℕ → ℕ) (μ : ℕ → ℕ → ℝ)
    (δ : ℝ) (r r' : ℕ)
    (hpt : ∀ n ∈ P, ∀ n' ∈ P, |μ n n'| ≤ δ + (if mf n = mf n' then (1 : ℝ) else 0)
      + (if o n = 1 ∧ o n' = 1 then (1 : ℝ) else 0)
      + (if o n = r ∧ o n' = r' then (1 : ℝ) else 0)
      + (if o n = r' ∧ o n' = r then (1 : ℝ) else 0)) :
    ∑ n ∈ P, ∑ n' ∈ P, c n * c n' * |μ n n'| ≤
      δ * (∑ n ∈ P, c n) ^ 2
      + ∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if mf n = mf n' then (1 : ℝ) else 0)
      + (∑ n ∈ P.filter (fun n => o n = 1), c n) ^ 2
      + 2 * ((∑ n ∈ P.filter (fun n => o n = r), c n) * (∑ n ∈ P.filter (fun n => o n = r'), c n)) := by sorry
