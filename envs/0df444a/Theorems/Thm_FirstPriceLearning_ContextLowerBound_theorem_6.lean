-- Prove2me | Theorems.Thm_FirstPriceLearning_ContextLowerBound_theorem_6
-- name    : FirstPriceLearning.ContextLowerBound.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:17.062163+00:00
-- url     : https://prove2.me/theorems/893675b2-ffe5-4c48-9048-de471d6035e0
-- title:
--   Theorem 6: with adversarial contexts and $K=(\alpha+1)M\le T^{1/3}$, every policy has regret $\ge\sqrt{KT}/(32e^3)$
-- statement:
--   Let $\alpha\ge1$ and $M\ge1$ be integers, let $K=(\alpha+1)M$, and let the horizon $T$ satisfy $K^3\le T$ and be a multiple of $M$. Then there is a feedback graph $G$ on $K$ actions, without self-loops, equal to its own transitive closure and with independence number exactly $\alpha$, with the following property. For every randomized non-anticipating policy $\pi$ there are a joint reward distribution $P$ on $[0,1]^{[M]\times[K]}$ and an oblivious context sequence $c_1,\dots,c_T\in[M]$ such that $(G,P)$, with the usual (total) order on the contexts, is a partially ordered contextual bandit with $\beta=1$ (Definition 3), and
--   $$\mathbb E[R_T(\pi)]\ \ge\ \frac{\sqrt{KT}}{32e^3}.$$
--
--   Since $\alpha M\le K$, we have $\sqrt{KT}\ge\sqrt{\alpha MT}\ge\min\{\sqrt{\alpha MT},\sqrt{KT},T^{2/3}\}$, so this yields the printed bound
--   $$\inf_\pi\sup_P\sup_{(c_t)}\mathbb E[R_T(\pi)]\ \ge\ c\min\{\sqrt{\alpha MT},\sqrt{KT},T^{2/3}\}$$
--   with the absolute constant $c=1/(32e^3)$ in this regime. It shows that under adversarial contexts the partially ordered structure cannot remove the polynomial dependence on $\min\{\alpha M,K\}$, in contrast with stochastic contexts (Theorem 5).
--
--   **Formalization Note.** This is the regime the paper's proof establishes ($K=(\alpha+1)M$, $K\le T^{1/3}$, $M\mid T$). The printed reduction from general $(M,K,T)$ by adding dummy contexts and actions is not formalized: it needs $K'=\min\{K,(\alpha+1)M,T^{1/3}\}\ge\alpha+1$, and the printed statement fails at $K=1$ (a single action has zero regret). Policies are randomized (internal randomness on an arbitrary probability space) and measurable; the order $\forall\pi\,\exists P\,\exists(c_t)$ is the infimum–supremum of the print with the supremum attained. Actions are `Fin K`, contexts `Fin M`.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 21, Theorem 6 (in the regime of its proof, pp. 21–24)

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model

open MeasureTheory

namespace FirstPriceLearning.ContextLowerBound

theorem theorem_6 (α M T : ℕ) (hα : 1 ≤ α) (hM : 1 ≤ M) (hK : ((α + 1) * M) ^ 3 ≤ T)
    (hMT : M ∣ T) :
    ∃ E : Fin ((α + 1) * M) → Fin ((α + 1) * M) → Prop,
      (∀ a, ¬ E a a) ∧ (∀ a b d, E a b → E b d → E a d) ∧ HasIndependenceNumber E α ∧
      ∀ (U : Type) [MeasurableSpace U] (μU : Measure U) [IsProbabilityMeasure μU]
        (π : Policy M (Fin ((α + 1) * M)) U),
        ∃ P : Measure (Fin M → Fin ((α + 1) * M) → ℝ),
          IsPartiallyOrderedContextualBandit E P (fun c₁ c₂ : Fin M => c₁ ≤ c₂) ∧
          HasOrderIndependenceNumber (fun c₁ c₂ : Fin M => c₁ ≤ c₂) 1 ∧
          ∃ c : Fin T → Fin M,
            Real.sqrt ((((α + 1) * M : ℕ) : ℝ) * T) / (32 * Real.exp 3) ≤
              expectedRegret E P μU π c := by sorry

end FirstPriceLearning.ContextLowerBound
