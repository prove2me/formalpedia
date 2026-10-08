-- Prove2me | Theorems.Thm_BoundedNV_Pooling_prop7_pooling_strict
-- name    : BoundedNV.Pooling.prop7_pooling_strict
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:03.246193+00:00
-- url     : https://prove2.me/theorems/ade9f4ab-0870-4f89-bba4-56715653a8bd
-- title:
--   Proposition 7, p. 585 — pooling strictly reduces behavioral expected costs
-- statement:
--   Consider $n\geq2$ locations with normally distributed demands of means $\mu_i$ and positive standard deviations $\sigma_i$. The total demand has mean $\mu_T=\sum_i\mu_i$ and standard deviation $\sigma_T$. Every decision maker has the same logit parameter $\beta>0$, holding cost $h>0$, and backlog penalty $b>0$. If
--
--   $$
--   \sigma_T\leq\sum_{i=1}^{n}\sigma_i,\qquad
--   \sigma_T\geq\sigma_i\quad\text{for every }i,
--   $$
--
--   then the expected cost of the pooled behavioral order is strictly smaller than the sum of the expected costs of separate behavioral orders:
--
--   $$
--   \mathbb E[\gamma_T(X_T^b)]<\sum_{i=1}^{n}\mathbb E[\gamma_i(X_i^b)].
--   $$
--
--   The strict gain includes perfectly correlated demands, for which pooling need not reduce the variance relative to the sum of individual standard deviations.
--
--   **Formalization Note** The theorem uses the normal marginals and the total-demand normal law, which are the only parts of the multivariate normal model used in the comparison. The paper leaves $n\geq2$ and $\sigma_i>0$ implicit, but both are necessary: with one location the two costs are equal, and a zero standard deviation makes the continuous logit law on its point support undefined. Utility is minus expected cost; it differs from the paper's profit by the additive constant $b\mu$. Positive costs ensure every normalizer and expected cost is genuine.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 585 (PDF 20), Proposition 7; §9 model p. 584 (PDF 19); proof pp. 587–588 (PDF 22–23)

import Mathlib
import Definitions.Def_BoundedNV_Pooling_Canonical

namespace BoundedNV.Pooling

/-- Proposition 7, p. 585: pooling strictly reduces the expected cost of logit orders. -/
theorem prop7_pooling_strict (n : ℕ) (μ σ : Fin n → ℝ) (σT h b β : ℝ)
    (hn : 2 ≤ n) (hσ : ∀ i, 0 < σ i)
    (hh : 0 < h) (hb : 0 < b) (hβ : 0 < β)
    (ha : σT ≤ ∑ i, σ i) (hb' : ∀ i, σ i ≤ σT) :
    behavioralCost h b β (∑ i, μ i) σT <
      ∑ i, behavioralCost h b β (μ i) (σ i) := by sorry

end BoundedNV.Pooling
