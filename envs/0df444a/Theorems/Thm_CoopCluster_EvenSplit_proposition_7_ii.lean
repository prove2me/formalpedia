-- Prove2me | Theorems.Thm_CoopCluster_EvenSplit_proposition_7_ii
-- name    : CoopCluster.EvenSplit.proposition_7_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:14.282256+00:00
-- url     : https://prove2.me/theorems/18c08a54-865c-4f2d-b41c-da0a5257870a
-- title:
--   Proposition 7(ii), p. 115 (PDF 10) — with t = 0, a threshold θc exists: ΠO ≥ ΠM iff θ ≤ θc, and ΠO < ΠM for θ > θc
-- statement:
--   Consider the service-cluster model under the standing assumptions, with the entertainment cost split evenly between the two providers ($t=0$). Let $\Pi^M$ be the optimal profit of the local monopolist, that is, the greatest element of $\{\Pi(p,\alpha):p\ge\gamma,\ \alpha\ge0\}$, and for $\theta\ge0$ let $\Pi^O(\theta)$ be a provider's profit at a symmetric equilibrium $(P^O,\alpha^O)$ of the co-opetition game with price-competition intensity $\theta$.
--
--   Then there is a threshold $\theta^c\ge 0$ such that, for every $\theta\ge0$ and every symmetric equilibrium at $\theta$,
--   $$\theta\le\theta^c\ \Longrightarrow\ \Pi^O(\theta)\ge\Pi^M,\qquad\qquad \theta>\theta^c\ \Longrightarrow\ \Pi^O(\theta)<\Pi^M .$$
--
--   Co-opetition is therefore at least as profitable as running the provider as a local monopolist exactly when price competition is mild: sharing the entertainment cost outweighs the loss from competing on price until the intensity $\theta$ passes $\theta^c$.
--
--   **Formalization Note.** $\Pi^O$ is the profit at a genuine symmetric equilibrium of the two-stage game (margins $P\ge0$, a joint optimum in the entertainment stage, no profitable deviation $P'\ge0$), and $\Pi^M$ is any greatest monopoly profit; neither is replaced by the closed forms of Propositions 1 and 3. One threshold serves all $\theta$. "The opposite holds" is read as the strict inequality $\Pi^O<\Pi^M$. The threshold is asked to be nonnegative; the page does not claim more. The strict capacity bound $\beta_0\gamma<B-hw$ replaces the page's weak one, without which the strict clause fails in a degenerate case (see the model file).
-- source:
--   Yuan, Dai, Chen & Gavirneni, Co-opetition in service clusters with waiting-area entertainment, MSOM 23(1):106–122 (2021), p. 115 (PDF 10), Proposition 7(ii)

import Mathlib
import Definitions.Def_CoopCluster_EvenSplit_Model

namespace CoopCluster.EvenSplit

theorem proposition_7_ii (M : Params) (hS : M.Standing) :
    ∃ θc : ℝ, 0 ≤ θc ∧
      ∀ θ : ℝ, 0 ≤ θ → ∀ P α : ℝ, IsSymEq M θ 0 P α →
        ∀ PiM : ℝ, IsGreatest (monoProfits M) PiM →
          (θ ≤ θc → PiM ≤ firmProfit M θ 0 α P P) ∧
          (θc < θ → firmProfit M θ 0 α P P < PiM) := by sorry

end CoopCluster.EvenSplit
