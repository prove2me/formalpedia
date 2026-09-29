-- Prove2me | Theorems.Thm_BanditAlgorithm_contextual_bandit_exp4_regret_bound
-- name    : BanditAlgorithm.contextual_bandit_exp4_regret_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-28T15:58:43.105774+00:00
-- url     : https://prove2.me/theorems/9dcd05e1-d628-45ba-ba21-3951df00a04f
-- statement:
--   (Exp4 regret bound, GOAL — L&S Theorem 18.1) Let $\gamma = 0$ and
--
--   $$\eta = \sqrt{\frac{2\log M}{nk}}.$$
--
--   For any adversarial rewards $x \in [0,1]^{n\times k}$ and any $M \ge 2$ oblivious experts whose advice rows lie in the probability simplex, the regret of Exp4 against the best expert satisfies
--
--   $$R_n \le \sqrt{2nk\log M}$$
--
--   (Eq. (18.7)).
-- source:
--   L&S Theorem 18.1, p.230

import Definitions.Def_ContextualAdversarialBandit
import Definitions.Def_exp4Policy


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.contextual_bandit_exp4_regret_bound
    {k M : ℕ} (hk : 0 < k) (hM : 1 < M) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (π : BanditPolicy k)
    (hπ : IsExp4Policy (Real.sqrt (2 * Real.log M / (n * k))) 0 E π) :
    exp4Regret n x E π ≤ Real.sqrt (2 * n * k * Real.log M) := by
  sorry
