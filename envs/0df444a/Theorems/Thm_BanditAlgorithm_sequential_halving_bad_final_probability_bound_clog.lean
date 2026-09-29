-- Prove2me | Theorems.Thm_BanditAlgorithm_sequential_halving_bad_final_probability_bound_clog
-- name    : BanditAlgorithm.sequential_halving_bad_final_probability_bound_clog
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T16:37:59.734456+00:00
-- url     : https://prove2.me/theorems/37279dcf-8749-425b-8862-8bc121bfd269
-- title:
--   Sequential Halving bad-final probability with $L$ phases
-- statement:
--   Let $L=\lceil\log_2 k\rceil$. For a sorted $1$-subgaussian bandit, budget $n\ge kL$, and complexity bound $i/\Delta_i^2\le H_2$, consider the event that a complete Sequential Halving active-set chain starts with an optimal arm but its final active set contains only suboptimal arms. Under any policy,
--
--   $$
--   \mathbb P(\text{no optimal arm survives})
--   \le 3L\exp\!\left(-\frac{n}{16H_2L}\right).
--   $$
--
--   This is the recommendation-independent concentration core of the general-$k$ Sequential Halving guarantee. It remains correct when several arms are optimal.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Exercise 33.8(c)–(f), printed pp. 419–420; direct general-k phase-count form.

import Definitions.Def_SequentialHalvingBadFinal

open MeasureTheory

theorem BanditAlgorithm.sequential_halving_bad_final_probability_bound_clog {k n : ℕ}
    (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (hsorted : ∀ i j : Fin k, i ≤ j → banditArmMean ν j ≤ banditArmMean ν i)
    (hn : k * Nat.clog 2 k ≤ n) (H₂ : ℝ)
    (hH₂ : ∀ i : Fin k, 0 < banditGap ν i →
      ((i : ℕ) + 1 : ℝ) / banditGap ν i ^ 2 ≤ H₂)
    (π : BanditPolicy k) :
    (banditMeasure ν π n).real {h | IsSeqHalvingBadFinalRun k n ν h} ≤
      3 * (Nat.clog 2 k : ℝ) *
        Real.exp (-(n / (16 * H₂ * (Nat.clog 2 k : ℝ)))) := by
  sorry
