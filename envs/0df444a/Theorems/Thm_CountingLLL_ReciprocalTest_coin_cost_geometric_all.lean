-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_coin_cost_geometric_all
-- name    : CountingLLL.ReciprocalTest.coin_cost_geometric_all
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:25:18.036672+00:00
-- url     : https://prove2.me/theorems/0d0f77e4-3085-423e-8f5c-cd613bb0eb24
-- title:
--   Operational Coin cost equals the geometric trial count
-- statement:
--   For every entropy tape, the number of oracle calls up to the first return of the operational local Coin equals the geometric trial count: the number of consecutive false oracle/fair-bit pairs, plus the terminating trial. Both sides are infinite when every pair is false. This is a pathwise coupling between the Algorithm 6 local machine and the IID trial model.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6 and proof of Lemma 6.5, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_CoinCost
open MeasureTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.coin_cost_geometric_all (ω : Entropy) :
    coinOracleCost ω = ∑' k : ℕ,
      ({x : ℕ → Bool × Bool | ∀ i < k, x i = (false,false)}).indicator
        (1 : (ℕ → Bool × Bool) → ℝ≥0∞) (fun i => (ω.1 i, ω.2.1 i)) := by sorry
