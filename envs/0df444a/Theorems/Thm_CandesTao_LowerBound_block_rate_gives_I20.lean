-- Prove2me | Theorems.Thm_CandesTao_LowerBound_block_rate_gives_I20
-- name    : CandesTao.LowerBound.block_rate_gives_I20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:44:40.988987+00:00
-- url     : https://prove2.me/theorems/1b951f51-72f7-4866-b7c4-c510a6478976
-- title:
--   Section II — $\pi_1 = (1-p)^\ell \le 2\delta/n$ gives (I.20)
-- statement:
--   Fix integers $1 \le m$ and $1 \le r \le n$, a real $\mu_0 \ge 1$ and $0 < \delta < 1/2$, and suppose that $\ell := n/(\mu_0 r)$ is an integer. Let $p = m/n^2$. If
--
--   $$(1-p)^{\ell} \le \frac{2\delta}{n},$$
--
--   then the sampling condition (I.20) holds:
--
--   $$m \ge n^2\left(1 - e^{-\frac{\mu_0 r}{n}\log\left(\frac{n}{2\delta}\right)}\right).$$
--
--   Here $(1-p)^\ell$ is the probability $\pi_1$ that a fixed row of a fixed $\ell$-wide diagonal block is unsampled under Bernoulli sampling with rate $p$. The statement is the "simple algebraic manipulation" of Candès and Tao that converts the bound $\pi_1 \le 2\delta/n$ into the sampling condition (I.20).
--
--   **Formalization Note** The integrality of $\ell$ is the paper's own "without loss of generality" assumption of Section II; it enters as a natural number `ℓ` with `(ℓ : ℝ) = n / (μ₀ r)`. The logarithm is natural.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2060, Section II ('With π₁ = (1 − p)^ℓ, a simple algebraic manipulation gives (I.20) under the Bernoulli model'); ℓ integral as assumed on p. 2059

import Definitions.Def_CandesTao_LowerBound_SamplingConditions

namespace CandesTao.LowerBound

theorem block_rate_gives_I20
    (n m r : ℕ) (μ₀ δ : ℝ) (ℓ : ℕ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hrn : r ≤ n) (hμ₀ : 1 ≤ μ₀)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hℓ : (ℓ : ℝ) = n / (μ₀ * r))
    (h : (1 - (m : ℝ) / (n : ℝ) ^ 2) ^ ℓ ≤ 2 * δ / n) :
    SamplingConditionI20 n m r μ₀ δ := by sorry

end CandesTao.LowerBound
