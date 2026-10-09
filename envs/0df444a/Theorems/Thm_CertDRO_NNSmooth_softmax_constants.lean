-- Prove2me | Theorems.Thm_CertDRO_NNSmooth_softmax_constants
-- name    : CertDRO.NNSmooth.softmax_constants
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:33:08.331375+00:00
-- url     : https://prove2.me/theorems/3607c41a-44b0-40c6-b8d3-a0a740bfae9b
-- title:
--   §B.9 — the softmax loss has gradient p(v) − e_y, Lipschitz constant √2 and smoothness constant 1
-- statement:
--   Let $K\ge1$, $y\in\{1,\dots,K\}$, and let $\sigma_y(v)=-\log p_y(v)$ be the softmax loss on $\mathbb R^K$, with $p(v)$ the vector of softmax probabilities. Then:
--
--   1. $\sigma_y$ is differentiable with gradient
--   $$\nabla\sigma_y(v)=p(v)-e_y ;$$
--   2. $\sigma_y$ is $\sqrt2$-Lipschitz: for all $u,v\in\mathbb R^K$,
--   $$|\sigma_y(u)-\sigma_y(v)|\le\sqrt2\,\|u-v\|_2 ;$$
--   3. if $K\ge2$, this constant is the supremum of the gradient norm:
--   $$\sup_{v\in\mathbb R^K}\|p(v)-e_y\|_2=\sqrt2 ;$$
--   4. the derivative of $\sigma_y$ is $1$-Lipschitz: for all $u,v\in\mathbb R^K$,
--   $$\|D\sigma_y(u)-D\sigma_y(v)\|_{\mathrm{op}}\le\|u-v\|_2 .$$
--
--   In the terminology of Assumption E, the softmax loss is a layer with $L^0=\sqrt2$ and $L^1=1$; these are the constants that enter Corollary 4.
--
--   **Formalization Note** The paper states $L^0=\sup_x\|p(x)-e_y\|_2=\sqrt2$; part 3 states this value of the supremum (a real supremum over a nonempty set bounded by $\sqrt2$), which is not attained, under $K\ge2$ (for $K=1$, $p\equiv e_y$ and the supremum is $0$; the paper's "any corner other than $e_y$" presumes a second class). The paper's "$L^1=1$" is a bound, not the value of a supremum, and is stated as a bound. The paper's eigenvalue argument for $L^1$ (via $\nabla^2\sigma_y=\operatorname{diag}p-pp^{T}$ and Weyl's inequality) is not formalized; only its conclusion, the bound with constant $1$, is. The derivative in part 4 is the Fréchet derivative, a linear functional whose operator norm equals the Euclidean norm of the gradient. Classes are `Fin K` (0-based) and $e_y$ is `EuclideanSpace.single y 1`.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 46, §B.9 (L0 = √2, L1 = 1)

import Mathlib
import Definitions.Def_CertDRO_NNSmooth_Softmax

namespace CertDRO.NNSmooth

/-- §B.9 (p. 46), the constants of the softmax loss `σ_y(v) = −log p_y(v)` on `ℝ^K`:
its gradient is `∇σ_y(v) = p(v) − e_y`; `σ_y` is `√2`-Lipschitz for the ℓ²-norm (`L⁰ = √2`);
for `K ≥ 2`, `sup_v ‖p(v) − e_y‖₂ = √2` (the supremum, not attained); and its derivative is
`1`-Lipschitz from the ℓ²-norm to the operator norm (`L¹ = 1`). -/
theorem softmax_constants {K : ℕ} (y : Fin K) :
    (∀ v : EuclideanSpace ℝ (Fin K),
      HasGradientAt (softmaxLoss y) (softmaxProb v - EuclideanSpace.single y 1) v) ∧
    (∀ u v : EuclideanSpace ℝ (Fin K),
      |softmaxLoss y u - softmaxLoss y v| ≤ Real.sqrt 2 * ‖u - v‖) ∧
    (2 ≤ K → (⨆ v : EuclideanSpace ℝ (Fin K),
      ‖softmaxProb v - EuclideanSpace.single y 1‖) = Real.sqrt 2) ∧
    (∀ u v : EuclideanSpace ℝ (Fin K),
      ‖fderiv ℝ (softmaxLoss y) u - fderiv ℝ (softmaxLoss y) v‖ ≤ 1 * ‖u - v‖) := by sorry

end CertDRO.NNSmooth
