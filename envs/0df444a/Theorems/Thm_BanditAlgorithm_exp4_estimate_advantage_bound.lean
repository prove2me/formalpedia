-- Prove2me | Theorems.Thm_BanditAlgorithm_exp4_estimate_advantage_bound
-- name    : BanditAlgorithm.exp4_estimate_advantage_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-28T23:59:25.66882+00:00
-- url     : https://prove2.me/theorems/cfbbb540-1a00-49a3-b4d0-6ff71e540bde
-- title:
--   Exp4 estimated-advantage bound
-- statement:
--   Let $k\ge 1$, $M\ge 2$, and $n\ge 1$, and let the learning rate satisfy $\eta>0$. In round $t$, let $x_{t,a}\in[0,1]$ be the reward of arm $a$, and let each expert advice row $(E_{t,m,a})_a$ be a probability distribution over the arms. Suppose the learner follows Exp4 with learning rate $\eta$ and exploration parameter $\gamma=0$.
--
--   For every fixed expert $m$, write $\widetilde S_{n,m}$ for its cumulative importance-weighted reward estimate and $\sum_{t=1}^{n}X_t$ for the learner’s collected reward. Then
--
--   $$
--   \mathbb{E}_{x,\pi}\!\left[\widetilde S_{n,m}\right]
--   -
--   \mathbb{E}_{x,\pi}\!\left[\sum_{t=1}^{n}X_t\right]
--   \le
--   \frac{\log M}{\eta}+\frac{\eta nk}{2}.
--   $$
--
--   This is the reusable potential-and-second-moment estimate for Exp4 before unbiasedness is substituted and the maximum over comparator experts is taken.
--
--   **Formalization Note** The two expectations are integrals over `adversarialMeasure`; `exp4Estimate` denotes $\widetilde S_{n,m}$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Theorem 18.1 proof, printed p. 230, Lemma 18.2 and Eqs. (18.9), (18.11), and (18.12). https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_ContextualAdversarialBandit
import Definitions.Def_exp4Policy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.exp4_estimate_advantage_bound
    {k M : ℕ} (hk : 0 < k) (hM : 1 < M) (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (π : BanditPolicy k)
    (hπ : IsExp4Policy η 0 E π)
    (m : Fin M) :
    (∫ h, exp4Estimate η 0 E n h m ∂(adversarialMeasure x π n)) -
        (∫ h, (∑ t, (h t).2) ∂(adversarialMeasure x π n)) ≤
      Real.log M / η + η * ((n : ℝ) * k) / 2 := by
  sorry
