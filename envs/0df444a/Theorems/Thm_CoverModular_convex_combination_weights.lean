-- Prove2me | Theorems.Thm_CoverModular_convex_combination_weights
-- name    : CoverModular.convex_combination_weights
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:13:36.254201+00:00
-- url     : https://prove2.me/theorems/c327dcf4-d6f2-440a-802c-82711fbb5fa3
-- title:
--   Proof of Proposition 2 — the weights $\pi_t=\frac{\delta}{K}(1-\frac2K)^{K-t}$ sum to 1 and give every $\rho_t$ the coefficient $\delta$
-- statement:
--   Let $K\ge1$ be an integer, $\delta=2/\bigl(1-(1-2/K)^K\bigr)$ and $\pi_t=\frac{\delta}{K}\bigl(1-\frac2K\bigr)^{K-t}$ for $t=1,\dots,K$. Then
--
--   1. $\pi_t\ge0$ for $t=1,\dots,K$, and $\sum_{1\le t\le K}\pi_t=1$;
--   2. for every sequence $(\rho_t)$,
--   $$
--   \sum_{t=1}^K\pi_t\Bigl(2\sum_{\tau=1}^{t-1}\rho_\tau+K\rho_t\Bigr)=\sum_{t=1}^K\rho_t\Bigl(K\pi_t+\sum_{\tau=t+1}^K2\pi_\tau\Bigr);
--   $$
--   3. for each $t=1,\dots,K$,
--   $$
--   K\pi_t+\sum_{\tau=t+1}^K2\pi_\tau=\delta\Bigl(1-\frac2K\Bigr)^{K-t}+\frac{2\delta}{K}\sum_{\tau=0}^{K-t-1}\Bigl(1-\frac2K\Bigr)^\tau=\delta .
--   $$
--
--   These are the convex-combination weights of the proof of Proposition 2: averaging the $K$ inequalities (14) with weights $\pi_t$ gives $F(\mathcal A^*)\le\delta F(\mathcal A_K)$. This item states the algebra of the weights; the inequality for $F$ is the goal theorem.
--
--   **Formalization Note** $2/K$ is real division; at $K=2$ the base is $0$ and $0^0=1$.
--
--   Differences from the source: none.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.2, proof of Proposition 2, p.16

import Mathlib

namespace CoverModular

/-- **The weights `π_t`** (DeValve, Pekeč, Wei, SSRN 3844987, §3.2, proof of Proposition 2,
p.16). For a positive integer `K` let `δ = 2/(1 − (1 − 2/K)^K)` and
`π_t = (δ/K)(1 − 2/K)^{K−t}`. Then `π_t ≥ 0` for `t = 1, …, K`, `∑_{1≤t≤K} π_t = 1`, for every
sequence `ρ` the exchange of summation
`∑_{t=1}^K π_t(2∑_{τ=1}^{t−1} ρ_τ + Kρ_t) = ∑_{t=1}^K ρ_t(Kπ_t + ∑_{τ=t+1}^K 2π_τ)` holds, and
`Kπ_t + ∑_{τ=t+1}^K 2π_τ = δ(1 − 2/K)^{K−t} + (2δ/K)∑_{τ=0}^{K−t−1}(1 − 2/K)^τ = δ` for each
`t = 1, …, K`.

**Formalization Note** `2/K` is real division with `K ≥ 1`; at `K = 2` the base is `0` and
`0^0 = 1`. -/
theorem convex_combination_weights (K : ℕ) (hK : 1 ≤ K) :
    let δ : ℝ := 2 / (1 - (1 - 2 / (K : ℝ)) ^ K)
    let π : ℕ → ℝ := fun t => δ / K * (1 - 2 / (K : ℝ)) ^ (K - t)
    (∀ t ∈ Finset.Icc 1 K, 0 ≤ π t) ∧
    ∑ t ∈ Finset.Icc 1 K, π t = 1 ∧
    (∀ ρ : ℕ → ℝ,
      ∑ t ∈ Finset.Icc 1 K, π t * (2 * ∑ τ ∈ Finset.Icc 1 (t - 1), ρ τ + K * ρ t) =
        ∑ t ∈ Finset.Icc 1 K, ρ t * (K * π t + ∑ τ ∈ Finset.Icc (t + 1) K, 2 * π τ)) ∧
    ∀ t ∈ Finset.Icc 1 K,
      K * π t + ∑ τ ∈ Finset.Icc (t + 1) K, 2 * π τ =
          δ * (1 - 2 / (K : ℝ)) ^ (K - t) +
            2 * δ / K * ∑ τ ∈ Finset.range (K - t), (1 - 2 / (K : ℝ)) ^ τ ∧
        δ * (1 - 2 / (K : ℝ)) ^ (K - t) +
            2 * δ / K * ∑ τ ∈ Finset.range (K - t), (1 - 2 / (K : ℝ)) ^ τ = δ := by sorry

end CoverModular
