-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_selfnormalised_fixed_count
-- name    : BanditAlgorithm.bandit_selfnormalised_fixed_count
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T20:35:19.528871+00:00
-- url     : https://prove2.me/theorems/5c99b1ab-f6c5-43e6-8e98-cf6056ddd65b
-- title:
--   Self-normalised deviation bound at a fixed pull count
-- statement:
--   The self-normalised deviation bound at a deterministic pull count: for a unit-variance Gaussian bandit, an arbitrary policy, an arm $a$, an integer $m\ge1$ and $\beta>0$,
--   $$\mathbb P\Bigl(T_a(n)=m\ \text{ and }\ \bigl(S_a(n)-T_a(n)\mu_a\bigr)^2\ge 2m\beta\Bigr)\ \le\ 2e^{-\beta}.$$
--
--   Since $\bigl(S_a(n)-T_a(n)\mu_a\bigr)^2/(2T_a(n))=\tfrac12 T_a(n)\bigl(\hat\mu_a(n)-\mu_a\bigr)^2$, the event is exactly a deviation of the self-normalised statistic appearing in Chernoff's stopping rule, at a fixed count. The proof splits by sign and applies the fixed-tilt Chernoff bound at $\lambda=\pm\sqrt{2\beta/m}$, the optimal tilt for the count $m$: on the event it makes $\tfrac{\lambda^2}{2}T_a(n)=\beta$ while $\lambda\bigl(S_a(n)-T_a(n)\mu_a\bigr)\ge2\beta$, so the martingale exponent already exceeds $\beta$.
-- source:
--   Standard optimisation of the Chernoff tilt at a deterministic pull count; see Garivier & Kaufmann, COLT 2016, Section 4.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory NNReal ENNReal
open scoped Classical

theorem BanditAlgorithm.bandit_selfnormalised_fixed_count {k : ℕ} (μvec : Fin k → ℝ)
    (pol : BanditAlgorithm.BanditPolicy k) (a : Fin k) (n : ℕ) {m : ℕ} (hm : 0 < m)
    {β : ℝ} (hβ : 0 < β) :
    BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | BanditAlgorithm.trajPullCount a n ω = m ∧
          2 * (m : ℝ) * β
            ≤ ((∑ s ∈ (Finset.range n).filter fun s ↦ (ω s).1 = a, (ω s).2)
                - (BanditAlgorithm.trajPullCount a n ω : ℝ) * μvec a) ^ 2}
      ≤ 2 * ENNReal.ofReal (Real.exp (-β)) := by
  sorry
