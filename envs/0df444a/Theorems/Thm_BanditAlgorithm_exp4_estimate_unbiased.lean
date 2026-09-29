-- Prove2me | Theorems.Thm_BanditAlgorithm_exp4_estimate_unbiased
-- name    : BanditAlgorithm.exp4_estimate_unbiased
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-28T23:57:26.769654+00:00
-- url     : https://prove2.me/theorems/44a59c04-e239-49f3-9214-0f749c9174bf
-- title:
--   Exp4 expert-score unbiasedness
-- statement:
--   Let $k\ge 1$, $M\ge 2$, and $n\ge 1$, and let the learning rate satisfy $\eta>0$. In round $t$, let $x_{t,a}\in[0,1]$ be the reward of arm $a$, and let each expert advice row $(E_{t,m,a})_a$ be a probability distribution over the arms. Suppose the learner follows Exp4 with learning rate $\eta$ and exploration parameter $\gamma=0$.
--
--   For every fixed expert $m$, let $\widetilde S_{n,m}$ be its cumulative importance-weighted reward estimate and let $S_{n,m}=\sum_{t=1}^{n}\sum_{a=1}^{k}E_{t,m,a}x_{t,a}$ be its true cumulative expected reward. Then
--
--   $$
--   \mathbb{E}_{x,\pi}\!\left[\widetilde S_{n,m}\right]
--   =
--   \sum_{t=1}^{n}\sum_{a=1}^{k}E_{t,m,a}x_{t,a}.
--   $$
--
--   Thus the score assigned by Exp4 to every fixed comparator expert is unbiased. This identity is reusable whenever an Exp4 potential bound must be translated into a bound against the experts’ actual rewards.
--
--   **Formalization Note** `exp4Estimate` is $\widetilde S_{n,m}$, `expertTotalReward` is $S_{n,m}$, and the expectation is integration against the adversarial interaction measure.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Theorem 18.1 proof, printed p. 230, Eq. (18.10). https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_ContextualAdversarialBandit
import Definitions.Def_exp4Policy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.exp4_estimate_unbiased
    {k M : ℕ} (hk : 0 < k) (hM : 1 < M) (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (π : BanditPolicy k)
    (hπ : IsExp4Policy η 0 E π)
    (m : Fin M) :
    (∫ h, exp4Estimate η 0 E n h m ∂(adversarialMeasure x π n)) =
      expertTotalReward n x E m := by
  sorry
