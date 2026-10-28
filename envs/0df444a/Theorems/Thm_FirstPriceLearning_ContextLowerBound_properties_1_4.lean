-- Prove2me | Theorems.Thm_FirstPriceLearning_ContextLowerBound_properties_1_4
-- name    : FirstPriceLearning.ContextLowerBound.properties_1_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:59.623008+00:00
-- url     : https://prove2.me/theorems/77107748-de49-42f1-87bf-228191f3287a
-- title:
--   Properties 1–4 of the mean rewards $R^u$ in the proof of Theorem 6
-- statement:
--   Let $K=(\alpha+1)M\le T$, $\Delta=\sqrt{K/(16T)}$, and $u\in\{0,1,\dots,\alpha\}^M$. Write $R^u_{c,a}$ for the mean reward of action $a$ under context $c$ for the Bernoulli product law $P^u$ of the proof of Theorem 6, and $\max_{a'}R^u_{c,a'}-R^u_{c,a}$ for the instantaneous regret of $a$ under $c$. Then:
--
--   1. every mean reward lies in $[0,1]$, and every non-zero mean reward lies in $[1/4,3/4]$;
--   2. under context $c$ the action $(c,u_c)$ is the unique optimal action: $R^u_{c,a}<R^u_{c,(c,u_c)}$ for every $a\ne(c,u_c)$;
--   3. every non-optimal action $a\ne(c,u_c)$ has instantaneous regret at least $\Delta$;
--   4. every action $(i,j)$ with $i\neq c$ has instantaneous regret at least $1/4$ under context $c$.
--
--   These are the four properties of the construction that turn regret into counts of wrong actions.
--
--   **Formalization Note.** The mean rewards are the integrals of the coordinates under the defined law $P^u$, so the statement also says that $P^u$ has the printed means. The hypothesis $K\le T$ is the printed $\Delta\le1/4$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 22, proof of Theorem 6, properties 1–4

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction

open MeasureTheory

namespace FirstPriceLearning.ContextLowerBound

theorem properties_1_4 (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) :
    (∀ (c : Fin M) (a : Act M α),
      meanReward (hardLaw M α T u) c a ∈ Set.Icc (0 : ℝ) 1 ∧
        (meanReward (hardLaw M α T u) c a ≠ 0 →
          meanReward (hardLaw M α T u) c a ∈ Set.Icc (1 / 4 : ℝ) (3 / 4))) ∧
    (∀ (c : Fin M) (a : Act M α), a ≠ (c, u c) →
      meanReward (hardLaw M α T u) c a < meanReward (hardLaw M α T u) c (c, u c)) ∧
    (∀ (c : Fin M) (a : Act M α), a ≠ (c, u c) →
      gap M α T ≤ optReward (hardLaw M α T u) c - meanReward (hardLaw M α T u) c a) ∧
    (∀ (c : Fin M) (a : Act M α), a.1 ≠ c →
      (1 / 4 : ℝ) ≤ optReward (hardLaw M α T u) c - meanReward (hardLaw M α T u) c a) := by sorry

end FirstPriceLearning.ContextLowerBound
