-- Prove2me | Theorems.Thm_BanditAlgorithm_exp4_regret_general_eta_bound
-- name    : BanditAlgorithm.exp4_regret_general_eta_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-28T21:10:21.432305+00:00
-- url     : https://prove2.me/theorems/cefa1548-06a7-4a39-9ac0-188e5c11eaf3
-- title:
--   Exp4 regret bound at a general learning rate
-- statement:
--   Let $k\ge 1$, $M\ge 2$, and $n\ge 1$. Let the learning rate satisfy $\eta>0$. In each round $t$, the adversarial reward vector has coordinates $x_{t,a}\in[0,1]$, and every expert advice row $E_t^{(m)}$ is a probability distribution over the $k$ arms. If the learner follows Exp4 with learning rate $\eta$ and exploration parameter $\gamma=0$, then its expected regret against the best of the $M$ oblivious experts satisfies
--
--   $$
--   R_n\le \frac{\log M}{\eta}+\frac{\eta nk}{2}.
--   $$
--
--   This is the reusable, pre-optimization form of the Exp4 regret theorem. Choosing the learning rate as a function of $n$, $k$, and $M$ yields the usual square-root regret bound.
--
--   **Formalization Note** The expected regret is `exp4Regret`; the predicate `IsExp4Policy` fixes the history-dependent policy to Algorithm 11.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Theorem 18.1 proof, printed p. 230, especially Eqs. (18.11) and (18.12), with the substitution immediately before Eq. (18.7).

import Definitions.Def_ContextualAdversarialBandit
import Definitions.Def_exp4Policy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.exp4_regret_general_eta_bound
    {k M : ℕ} (hk : 0 < k) (hM : 1 < M) (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (π : BanditPolicy k)
    (hπ : IsExp4Policy η 0 E π) :
    exp4Regret n x E π ≤
      Real.log M / η + η * ((n : ℝ) * k) / 2 := by
  sorry
