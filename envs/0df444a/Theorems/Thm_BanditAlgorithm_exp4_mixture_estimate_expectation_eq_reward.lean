-- Prove2me | Theorems.Thm_BanditAlgorithm_exp4_mixture_estimate_expectation_eq_reward
-- name    : BanditAlgorithm.exp4_mixture_estimate_expectation_eq_reward
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T00:14:06.809073+00:00
-- url     : https://prove2.me/theorems/54cca631-c30a-4442-8563-141c5d9f1424
-- title:
--   Exp4 mixture score equals expected reward
-- statement:
--   Let $k\ge1$, $M\ge2$, $n\ge1$, and $\eta>0$. Let rewards satisfy $x_{t,a}\in[0,1]$, let every expert advice row be a probability distribution, and suppose the learner follows Exp4 with exploration parameter $\gamma=0$. If $Q_{t,m}$ is the exponential weight of expert $m$ and $\widetilde X_{t,m}$ is its one-round importance-weighted score, then
--
--   $$
--   \mathbb E\!\left[\sum_{t=1}^{n}\sum_{m=1}^{M}Q_{t,m}\widetilde X_{t,m}\right]
--   =
--   \mathbb E\!\left[\sum_{t=1}^{n}X_t\right].
--   $$
--
--   Thus the Exp4 mixture score has exactly the learner’s expected collected reward. This identity converts the linear term in the potential inequality into the regret benchmark.
--
--   **Formalization Note** The left process is `exp4MixtureEstimate`; the right process sums the reward coordinate of the bandit history.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Theorem 18.1 proof, printed p. 230, Eq. (18.10) and the conditional-expectation step leading to Eq. (18.11). https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_ContextualAdversarialBandit
import Definitions.Def_exp4Analysis

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.exp4_mixture_estimate_expectation_eq_reward
    {k M : ℕ} (hk : 0 < k) (hM : 1 < M) (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (π : BanditPolicy k)
    (hπ : IsExp4Policy η 0 E π) :
    (∫ h, exp4MixtureEstimate η E n h ∂(adversarialMeasure x π n)) =
      ∫ h, (∑ t, (h t).2) ∂(adversarialMeasure x π n) := by
  sorry
