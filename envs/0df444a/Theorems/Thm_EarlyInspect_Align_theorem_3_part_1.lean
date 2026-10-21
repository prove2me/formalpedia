-- Prove2me | Theorems.Thm_EarlyInspect_Align_theorem_3_part_1
-- name    : EarlyInspect.Align.theorem_3_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:18.023329+00:00
-- url     : https://prove2.me/theorems/6d4e7651-6709-4f5d-976d-731d1dcbaad6
-- title:
--   Theorem 3 part 1, p. 63 — if M > Φ(−k)√tσ/φ(−k√t), ω has a unique root z′ ≥ −k and the agent's optimum is z* = max(z′, z^I)
-- statement:
--   Let the period demand be $D\sim N(\mu,\sigma^2)$ with $\sigma>0$, let $t\in(0,1)$ be the inspection time, $Y_t\sim N(t\mu,t\sigma^2)$, and let the agent minimize, over order-up-to levels $S\ge I$, his expected score under scheme $[M,t]$ with $\hat c_o=1$,
--   $$\mathrm{ETPM}_{[Mt]}(S)=\mathbb E\big[(S-D)^+\big]+M\,\mathbb P\{Y_t\ge S\},$$
--   where $I\ge0$ is the starting inventory level. Write $k=\mu/\sigma$, $z^I=(I-\mu)/\sigma$ and let $\omega$ be the function of eq. (9). If
--   $$M>\frac{\Phi(-k)}{\varphi(-k\sqrt t)}\sqrt t\,\sigma,$$
--   then there is exactly one $z'\ge-k$ with $\omega(z')=0$, and the agent's problem has the unique solution $S^{a*}=\mu+\sigma z^*$ with
--   $$z^*=\max(z',z^I),$$
--   that is, $z^*=z'$ if $z'\ge z^I$ and $z^*=z^I$ otherwise.
--
--   This is the characterization of the agent's response used in §4.2.2, where the principal assumes that the posted $M$ satisfies this inequality in every state.
--
--   **Formalization Note** The uniqueness of the root is on $z\ge-k$, that is on stock levels $S\ge0$: as $z\to-\infty$, $\omega(z)\to0^+$, so $\omega$ has a further root below $-k$, and the page's "unique" is read on the feasible region. Starting inventory is nonnegative ($I\ge0$, p. 64), so $z^I\ge-k$. The agent's optimum is the set of minimizers of the score over $[I,\infty)$, stated as the singleton $\{\mu+\sigma\max(z',z^I)\}$, which includes uniqueness.
-- source:
--   Alp & Şen, Delegation of Stocking Decisions Under Asymmetric Demand Information, M&SOM 23(1):55–69 (2021), p. 63 (PDF 10), Theorem 3 part 1

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_EarlyInspect_Align_Model

namespace EarlyInspect.Align

theorem theorem_3_part_1 (μ σ M t I : ℝ) (hσ : 0 < σ) (ht : 0 < t) (ht1 : t < 1) (hI : 0 ≤ I)
    (hM : Φ (-(μ / σ)) / φ (-(μ / σ) * Real.sqrt t) * Real.sqrt t * σ < M) :
    ∃ z' : ℝ, (-(μ / σ) ≤ z' ∧ omega μ σ M t z' = 0) ∧
      (∀ z'' : ℝ, -(μ / σ) ≤ z'' → omega μ σ M t z'' = 0 → z'' = z') ∧
      argminFrom (agentCost μ σ M t) I = {μ + σ * max z' ((I - μ) / σ)} := by sorry

end EarlyInspect.Align
