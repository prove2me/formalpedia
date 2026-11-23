-- Prove2me | Theorems.Thm_EarlyInspect_Align_Supplement_theorem_3_part_2
-- name    : EarlyInspect.Align.Supplement.theorem_3_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:42:03.702639+00:00
-- url     : https://prove2.me/theorems/589ef20c-9d0d-453d-876c-7fa791f5af1f
-- title:
--   Theorem 3.2, p. 63 — below both thresholds of $M$ the agent under early inspection does not order: $z^*=z^I$
-- statement:
--   Let the period demand be $D\sim N(\mu,\sigma^2)$ with $\sigma>0$, let $t\in(0,1)$ be the inspection time and $Y_t\sim N(t\mu,t\sigma^2)$ the demand up to time $t$. The agent starts with inventory $I\ge0$ and, under scheme $[M,t]$ with $\hat c_o=1$, minimizes over order-up-to levels $S\ge I$ the score
--
--   $$
--   \mathrm{ETPM}_{[Mt]}(S)=\mathbb E\big[(S-D)^+\big]+M\,\mathbb P\{Y_t\ge S\}.
--   $$
--
--   Write $\Phi$ and $\varphi$ for the standard normal distribution function and density, $k=\mu/\sigma$ and $z^I=(I-\mu)/\sigma$. Suppose that
--
--   $$
--   M<\frac{\Phi(-k)}{\varphi(-k\sqrt t)}\sqrt t\,\sigma\qquad\text{and}\qquad M<\frac{e^{-\frac12k^2(1-t)}\sqrt t\,\sigma}{k}.
--   $$
--
--   Then the agent does not order: the only optimal standardized level is $z^*=z^I$, that is
--
--   $$
--   \operatorname*{argmin}_{S\ge I}\mathrm{ETPM}_{[Mt]}(S)=\{I\}.
--   $$
--
--   This is rule 2 of the paper's Theorem 3. It identifies the penalties that are too small to make the agent replenish.
--
--   **Formalization Note** The two thresholds are written as in the published Lemma 1 and Theorem 3 part 1. No sign is imposed on $\mu$ or $M$. For $\mu<0$ the second threshold is negative. At $\mu=0$ Lean evaluates it as $0$, because division by zero returns zero. In both cases the hypotheses then allow only negative $M$.
--
--   Differences from the source:
--   - reading: the starting inventory level is I → I ≥ 0; reason: starting inventory is nonnegative in the paper (Figure 1; p. 64, "for all I^N ≥ 0"), as in the published rule 1
--   - generalization: thresholds written with a division by k = μ/σ, hence defined for μ ≠ 0 → every real μ, the threshold with 1/k being read as 0 at μ = 0; reason: nothing changes when μ ≠ 0, so every instance of the source is covered, and the conclusion also holds at μ = 0
--   - encoding: the optimal standardized level z∗ = (S − μ)/σ → the set of minimizers S ≥ I of the score, with z∗ = z^I written as S = I; reason: S ↦ (S − μ)/σ is a bijection because σ > 0
--   - generalization: M is a stock-out penalty, constrained to M ≥ 0 in the principal’s problems (6) and (11) → M may be any real number satisfying the displayed threshold inequalities; reason: this retains every nonnegative-penalty instance; for M ≤ 0, omega is strictly positive and the score is strictly increasing, so the same conclusions also hold
-- source:
--   Alp & Şen, Delegation of Stocking Decisions Under Asymmetric Demand Information, M&SOM 23(1):55–69 (2021), p. 63 (PDF 10), §4.2.1, Theorem 3 part 2

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_EarlyInspect_Align_Model

namespace EarlyInspect.Align.Supplement

theorem theorem_3_part_2 (μ σ M t I : ℝ) (hσ : 0 < σ) (ht : 0 < t) (ht1 : t < 1) (hI : 0 ≤ I)
    (hM₁ : M < Φ (-(μ / σ)) / φ (-(μ / σ) * Real.sqrt t) * Real.sqrt t * σ)
    (hM₂ : M < Real.exp (-(1 / 2) * ((μ / σ) ^ 2 * (1 - t))) * Real.sqrt t * σ / (μ / σ)) :
    argminFrom (agentCost μ σ M t) I = {I} := by sorry

end EarlyInspect.Align.Supplement
