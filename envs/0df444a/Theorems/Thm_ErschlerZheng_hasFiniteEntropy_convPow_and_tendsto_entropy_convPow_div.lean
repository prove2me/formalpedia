-- Prove2me | Theorems.Thm_ErschlerZheng_hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div
-- name    : ErschlerZheng.hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-05T22:06:28.227851+00:00
-- url     : https://prove2.me/theorems/8ddac66b-2765-4378-a8bc-8913a68482ff
-- title:
--   p. 10 — for a probability of finite entropy, every H(μ^(n)) is finite and H(μ^(n))/n converges: the Avez asymptotic entropy exists
-- statement:
--   Let $\Gamma$ be a countable group and $\mu$ a probability on $\Gamma$ (`IsProbability`) of finite entropy (`HasFiniteEntropy`: $\sum_g -\mu(g)\log\mu(g) < \infty$). Then every convolution power $\mu^{(n)}$ (`convPow`) has finite entropy, and
--   $$\frac{H(\mu^{(n)})}{n} \longrightarrow \mathbf h_\mu \qquad (n \to \infty),$$
--   where $H$ is the Shannon entropy (`entropy`) and $\mathbf h_\mu$ the asymptotic entropy (`asymptoticEntropy`). Since `asymptoticEntropy μ` is defined as the limit of this sequence whenever the limit exists, the second part says exactly that $H(\mu^{(n)})/n$ converges to a real number.
--
--   Erschler and Zheng, p. 10: “In the case that the measure $\mu$ has finite entropy $H(\mu) < \infty$, the (Avez) *asymptotic entropy* of $\mu$ is defined as $\mathbf h_\mu = \lim_{n \to \infty} \frac{H(\mu^{(n)})}{n}$.”
--
--   The sentence takes for granted that each $H(\mu^{(n)})$ is finite and that the limit exists; the statement is those two claims.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 10, the Avez entropy

import Mathlib
import Definitions.Def_ErschlerZheng_Walks

namespace ErschlerZheng

theorem hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div {Γ : Type*} [Group Γ]
    [Countable Γ] (μ : Γ → ℝ) (hμ : IsProbability μ) (hH : HasFiniteEntropy μ) :
    (∀ n : ℕ, HasFiniteEntropy (convPow μ n)) ∧
    Filter.Tendsto (fun n : ℕ => entropy (convPow μ n) / n) Filter.atTop
      (nhds (asymptoticEntropy μ)) := by
  sorry

end ErschlerZheng
