-- Prove2me | Theorems.Thm_BurkholderDFI_ConvexPhi_eq_14_5
-- name    : BurkholderDFI.ConvexPhi.eq_14_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:07.919376+00:00
-- url     : https://prove2.me/theorems/e960c131-2574-455d-a675-3ac12b0c7863
-- title:
--   (14.5) — total magnitude of Davis large jumps
-- statement:
--   For the large-jump sequence $z_k=d_k\mathbf1_{\{|d_k|>2d_{k-1}^*\}}$ associated with any real process,
--   $$
--   \sum_{k\ge1}|z_k|\le2d^*,
--   \qquad d^*=\sup_{k\ge1}|d_k|.
--   $$
--   The estimate is pathwise and does not require a probability measure.
--
--   **Formalization Note** Both sides are extended nonnegative quantities, so the statement also covers an unbounded sequence of jumps.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), (14.5), p. 33

import Mathlib
import Definitions.Def_BurkholderDFI_ConvexPhi_Davis

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (14.5), p. 33: the large jumps telescope against d*. -/
theorem eq_14_5 {Ω : Type*} [mΩ : MeasurableSpace Ω] (f : ℕ → Ω → ℝ) :
    ∀ ω, (∑' k : ℕ, ENNReal.ofReal |davisZ f (k + 1) ω|) ≤
      2 * BurkholderDFI.SquareFnLp.maxFn (BurkholderDFI.SquareFnLp.dseq f) ω := by sorry
end BurkholderDFI.ConvexPhi
