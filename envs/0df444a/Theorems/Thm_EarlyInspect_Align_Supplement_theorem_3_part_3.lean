-- Prove2me | Theorems.Thm_EarlyInspect_Align_Supplement_theorem_3_part_3
-- name    : EarlyInspect.Align.Supplement.theorem_3_part_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:43:01.262669+00:00
-- url     : https://prove2.me/theorems/d7f72a59-44f3-464f-97c1-8939f6dd005c
-- title:
--   Theorem 3.3, p. 63 — between the two thresholds of $M$, $\omega$ has at most two roots and the optimum $z^*$ is one of them or $z^I$
-- statement:
--   Let the period demand be $D\sim N(\mu,\sigma^2)$ with $\sigma>0$, let $t\in(0,1)$ be the inspection time and $Y_t\sim N(t\mu,t\sigma^2)$ the demand up to time $t$. The agent starts with inventory $I\ge0$ and, under scheme $[M,t]$ with $\hat c_o=1$, minimizes over order-up-to levels $S\ge I$ the score
--
--   $$
--   \mathrm{ETPM}_{[Mt]}(S)=\mathbb E\big[(S-D)^+\big]+M\,\mathbb P\{Y_t\ge S\}.
--   $$
--
--   Write $\Phi$ and $\varphi$ for the standard normal distribution function and density, $k=\mu/\sigma$ and $z^I=(I-\mu)/\sigma$. With $a=k(1-t)$, let $\omega$ be the function of eq. (9),
--
--   $$
--   \omega(z)=\Phi(z)-\frac{M}{\sqrt t\,\sigma}\,\varphi\!\left(\frac{a+z}{\sqrt t}\right),\qquad z\in\mathbb R.
--   $$
--
--   Suppose that
--
--   $$
--   \frac{e^{-\frac12k^2(1-t)}\sqrt t\,\sigma}{k}<M<\frac{\Phi(-k)}{\varphi(-k\sqrt t)}\sqrt t\,\sigma.
--   $$
--
--   Then:
--
--   1. at most two real numbers $z'$ satisfy $\omega(z')=0$;
--   2. the agent's problem has an optimal solution;
--   3. every optimal level $S\ge I$, with $z^*=(S-\mu)/\sigma$, satisfies $\omega(z^*)=0$ or $z^*=z^I$.
--
--   This is rule 3 of the paper's Theorem 3, which completes the description of the agent's response to $[M,t]$. Its range of penalties is empty when $\mu>0$, by the Mills-ratio inequality $\Phi(-k)<\varphi(k)/k$. It is nonempty when $\mu\le0$, and is therefore stated for every real $\mu$.
--
--   **Formalization Note** The roots are counted on the whole real line, as printed, with `Set.encard`, so "at most two" includes finiteness. This is stronger than a count on $z\ge-k$ (stock levels $S\ge0$), the domain on which the published rule 1 asserts uniqueness. A minimizer satisfies $S\ge I\ge0$, so a root that it attains has $z\ge z^I\ge-k$. Existence of a minimizer is stated separately, so the last clause is not vacuous. At $\mu=0$ Lean evaluates the lower threshold as $0$.
--
--   Differences from the source:
--   - reading: the starting inventory level is I → I ≥ 0; reason: starting inventory is nonnegative in the paper (Figure 1; p. 64, "for all I^N ≥ 0"), as in the published rule 1
--   - generalization: thresholds written with a division by k = μ/σ, hence defined for μ ≠ 0 → every real μ, the threshold with 1/k being read as 0 at μ = 0; reason: nothing changes when μ ≠ 0, so every instance of the source is covered, and the conclusion also holds at μ = 0
--   - encoding: the optimal standardized level z∗ = (S − μ)/σ → the set of minimizers S ≥ I of the score, with z∗ = z^I written as S = I; reason: S ↦ (S − μ)/σ is a bijection because σ > 0
--   - generalization: M is a stock-out penalty, constrained to M ≥ 0 in the principal’s problems (6) and (11) → M may be any real number satisfying the displayed threshold inequalities; reason: this retains every nonnegative-penalty instance; for M ≤ 0, omega is strictly positive and the score is strictly increasing, so the same conclusions also hold
-- source:
--   Alp & Şen, Delegation of Stocking Decisions Under Asymmetric Demand Information, M&SOM 23(1):55–69 (2021), p. 63 (PDF 10), §4.2.1, Theorem 3 part 3

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_EarlyInspect_Align_Model

namespace EarlyInspect.Align.Supplement

theorem theorem_3_part_3 (μ σ M t I : ℝ) (hσ : 0 < σ) (ht : 0 < t) (ht1 : t < 1) (hI : 0 ≤ I)
    (hM₁ : Real.exp (-(1 / 2) * ((μ / σ) ^ 2 * (1 - t))) * Real.sqrt t * σ / (μ / σ) < M)
    (hM₂ : M < Φ (-(μ / σ)) / φ (-(μ / σ) * Real.sqrt t) * Real.sqrt t * σ) :
    {z : ℝ | omega μ σ M t z = 0}.encard ≤ 2 ∧
      (argminFrom (agentCost μ σ M t) I).Nonempty ∧
      ∀ S ∈ argminFrom (agentCost μ σ M t) I,
        omega μ σ M t ((S - μ) / σ) = 0 ∨ S = I := by sorry

end EarlyInspect.Align.Supplement
