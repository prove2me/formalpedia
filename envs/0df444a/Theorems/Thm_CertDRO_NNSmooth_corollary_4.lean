-- Prove2me | Theorems.Thm_CertDRO_NNSmooth_corollary_4
-- name    : CertDRO.NNSmooth.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:34:10.777991+00:00
-- url     : https://prove2.me/theorems/1e208f1a-ac41-4535-8eb6-79895ed4e23c
-- title:
--   Corollary 4 — the softmax loss of a smooth deep network has a (√2·β_L(θ)+α_L(θ)²)-Lipschitz input gradient
-- statement:
--   Let a network of depth $L$ with logits $F_L(\theta;x)\in\mathbb R^K$ satisfy Assumption E with layer constants $L^0_l, L^1_l$, and let $\alpha_L(\theta)$, $\beta_L(\theta)$ be given by (21). For a class $y\in\{1,\dots,K\}$ consider the softmax loss (19)
--   $$\ell(\theta;(x,y))=-\log p_y(\theta;x),\qquad p_y(\theta;x)=\frac{\exp(F_{L,y}(\theta;x))}{\sum_{k=1}^{K}\exp(F_{L,k}(\theta;x))}.$$
--   Then the input gradient $x\mapsto\nabla_x\ell(\theta;(x,y))$ is $\big(\sqrt2\,\beta_L(\theta)+\alpha_L(\theta)^2\big)$-Lipschitz: for all inputs $x,x'$,
--   $$\big\|\nabla_x\ell(\theta;(x,y))-\nabla_x\ell(\theta;(x',y))\big\|_2\le\big(\sqrt2\,\beta_L(\theta)+\alpha_L(\theta)^2\big)\,\|x-x'\|_2 .$$
--
--   This bounds the input-smoothness constant $L_{zz}$ of a deep classifier in terms of its weights' spectral norms and the layer constants, and with it the penalty $\gamma>L_{zz}$ beyond which the paper's Wasserstein-robust training problem has a strongly concave inner maximization and its certificates apply.
--
--   **Formalization Note** The input gradient is Mathlib's `gradient` (the Riesz representative of the Fréchet derivative) on $\mathbb R^p=\mathbb R^{d_{0,O}}$; its Euclidean norm equals the operator norm of the derivative, so the paper's "w.r.t. $(\|\cdot\|_{\mathrm{op}},\|\cdot\|_2)$" is this bound. The number of classes is the output width $K=d_{L,O}$, and $y$ is a class index (0-based), so $K\ge1$. The constants $\alpha_L,\beta_L$ are the explicit products and sums of (21), not free parameters. Assumption E includes the differentiability of each $\sigma_l$ and $L^0_l>0$, $L^1_l\ge0$.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 13, Corollary 4; proof p. 46, §B.9

import Mathlib
import Definitions.Def_CertDRO_NNSmooth_Network
import Definitions.Def_CertDRO_NNSmooth_Softmax

namespace CertDRO.NNSmooth

open Network

/-- Corollary 4 (p. 13; proof §B.9, p. 46). Under Assumption E for the `L` layers of the network,
for every class `y` the input gradient `x ↦ ∇_x ℓ(θ; (x, y))` of the softmax loss (19),
`ℓ(θ; (x, y)) = −log p_y(θ; x)` with logits `F_L(θ; x) ∈ ℝ^K`, `K = d_{L,O}`, is
`(√2 β_L(θ) + α_L(θ)²)`-Lipschitz for the ℓ²-norm, with `α_L, β_L` given by (21). -/
theorem corollary_4 (N : Network) (L : ℕ) (L0 L1 : ℕ → ℝ) (hE : N.AssumptionE L L0 L1)
    (y : Fin (N.dO L)) (x x' : E (N.dO 0)) :
    ‖gradient (fun z => softmaxLoss y (N.F L z)) x - gradient (fun z => softmaxLoss y (N.F L z)) x'‖
      ≤ (Real.sqrt 2 * N.β L0 L1 L + N.α L0 L ^ 2) * ‖x - x'‖ := by sorry

end CertDRO.NNSmooth
