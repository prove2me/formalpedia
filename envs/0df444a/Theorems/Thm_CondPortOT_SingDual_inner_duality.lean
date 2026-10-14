-- Prove2me | Theorems.Thm_CondPortOT_SingDual_inner_duality
-- name    : CondPortOT.SingDual.inner_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:02.599635+00:00
-- url     : https://prove2.me/theorems/7bf7178d-acfc-455f-807a-0bd9a9e956ad
-- title:
--   Proof of Theorem 3.2, p. 41 — for fixed υ with Συᵢ𝔻_𝒳(x₀,x̂ᵢ) < Nρ the inner sup equals its moment dual over (λ₁, θ)
-- statement:
--   Let $\varepsilon\in(0,1]$, $N\ge1$, Assumption 2.4 with $\gamma=0$, $\ell:\mathcal Y\to\mathbb R$ measurable, and $\upsilon\in[0,1]^N$ with $\sum_i\upsilon_i=N\varepsilon$ and
--   $$\sum_{i\in[N]}\upsilon_i\,\mathbb D_{\mathcal X}(x_0,\hat x_i)<N\rho .$$
--   Then the inner supremum
--   $$\sup\Big\{(N\varepsilon)^{-1}\sum_i\upsilon_i\mathbb E_{\mu_0^i}[\ell(Y)]:\ \mu_0^i\in\mathcal M(\mathcal Y),\ \sum_i\upsilon_i\big(\mathbb D_{\mathcal X}(x_0,\hat x_i)+\mathbb E_{\mu_0^i}[\mathbb D_{\mathcal Y}(Y,\hat y_i)]\big)\le N\rho\Big\}$$
--   equals
--   $$\inf\Big\{\lambda_1\Big(N\rho-\sum_i\upsilon_i\mathbb D_{\mathcal X}(x_0,\hat x_i)\Big)+\sum_i\theta_i:\ \lambda_1\ge0,\ \theta\in\mathbb R^N,\ \upsilon_i\mathbb D_{\mathcal Y}(y_i,\hat y_i)\lambda_1+\theta_i\ge(N\varepsilon)^{-1}\upsilon_i\ell(y_i)\ \ \forall y_i\in\mathcal Y,\ i\in[N]\Big\}.$$
--
--   This is the moment-problem strong duality the proof of Theorem 3.2 applies for each fixed weight vector, before exchanging the order of optimization.
--
--   **Formalization Note** The page asserts this for every $\upsilon$ in $\mathcal U=\{\upsilon\in[0,1]^N:\sum_i\upsilon_i=N\varepsilon,\ \sum_i\upsilon_i\kappa_i\le N\rho\}$, justified by the Slater point $\mu_0^i=\delta_{\hat y_i}$. That point is strictly feasible only when $\sum_i\upsilon_i\kappa_i<N\rho$ (at $\gamma=0$, $\kappa_i=\mathbb D_{\mathcal X}(x_0,\hat x_i)$), and on the boundary the duality can fail for a loss that is not upper semicontinuous; the statement is therefore posed with the strict inequality. Measurability of $\ell$ is added, as in Proposition A.5. The left side is `innerSup`, the right side `innerDual`, both in $[-\infty,\infty]$.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 41, proof of Theorem 3.2, "The duality result for moment problem [74, Proposition 3.4] implies that the inner supremum problem is equivalent to"

import Mathlib
import Definitions.Def_CondPortOT_SingDual_Setting

open MeasureTheory

namespace CondPortOT.SingDual

theorem inner_duality {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (hA : Assumption24 DX DY x0 0 xh) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ρ : ℝ)
    (L : Y → ℝ) (hL : Measurable L) (υ : Fin N → ℝ) (hυ : ∀ i, υ i ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∑ i, υ i = N * ε) (hslater : ∑ i, υ i * DX x0 (xh i) < N * ρ) :
    innerSup DX DY xh yh x0 ρ ε L υ = innerDual DX DY xh yh x0 ρ ε L υ := by sorry

end CondPortOT.SingDual
