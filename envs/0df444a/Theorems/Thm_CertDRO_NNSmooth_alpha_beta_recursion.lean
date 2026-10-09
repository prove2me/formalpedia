-- Prove2me | Theorems.Thm_CertDRO_NNSmooth_alpha_beta_recursion
-- name    : CertDRO.NNSmooth.alpha_beta_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:33:44.968422+00:00
-- url     : https://prove2.me/theorems/d5f190a8-cd53-4170-949e-881c0d0aea37
-- title:
--   §B.9 — recursion for α_l(θ), β_l(θ), and β_{L+1}(θ) = √2β_L(θ) + α_L(θ)² for a softmax output layer
-- statement:
--   Let $\alpha_l(\theta)$ and $\beta_l(\theta)$ be the constants (21) of a network with layer constants $L^0_l, L^1_l$. Then:
--
--   1. $\alpha_0(\theta)=1$ and $\beta_0(\theta)=0$;
--   2. for every $l\ge0$,
--   $$\alpha_{l+1}(\theta)=L^0_{l+1}\|\theta_{l+1}\|_{\mathrm{op}}\,\alpha_l(\theta);$$
--   3. for every $l\ge0$,
--   $$\beta_{l+1}(\theta)=L^0_{l+1}\|\theta_{l+1}\|_{\mathrm{op}}\,\beta_l(\theta)+\frac{L^1_{l+1}}{(L^0_{l+1})^2}\,\alpha_{l+1}(\theta)^2 ;$$
--   4. whenever $\alpha_l(\theta)\ne0$, equivalently
--   $$\beta_{l+1}(\theta)=\frac{\alpha_{l+1}(\theta)}{\alpha_l(\theta)}\,\beta_l(\theta)+\frac{L^1_{l+1}}{(L^0_{l+1})^2}\,\alpha_{l+1}(\theta)^2 ;$$
--   5. if an $(L+1)$-st layer has $\|\theta_{L+1}\|_{\mathrm{op}}=1$ (for instance $\theta_{L+1}=I$), $L^0_{L+1}=\sqrt2$ and $L^1_{L+1}=1$ (the softmax loss), then
--   $$\beta_{L+1}(\theta)=\sqrt2\,\beta_L(\theta)+\alpha_L(\theta)^2 .$$
--
--   Part 5 is how the paper reads off the constant of Corollary 4: the softmax loss is treated as one more layer of the network.
--
--   **Formalization Note** The paper writes "with $\beta_0(\theta)=\alpha_0(\theta)=1$"; that is a misprint, since (21) gives $\beta_0=0$ (empty sum) and $\alpha_0=1$, and the formalization follows (21). The paper's ratio $\alpha_{l+1}/\alpha_l$ is undefined when some $\theta_j=0$; part 3 states what the ratio means without dividing, and part 4 is the paper's form under $\alpha_l\ne0$. In Lean layers are 0-based (`θ l`, `L0 l`, `L1 l` are the paper's $\theta_{l+1}$, $L^0_{l+1}$, $L^1_{l+1}$), and in part 5 the identity layer enters only through $\|\theta_{L+1}\|_{\mathrm{op}}=1$.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 46, §B.9 (recursive form of (21) and β_{L+1})

import Mathlib
import Definitions.Def_CertDRO_NNSmooth_Network

namespace CertDRO.NNSmooth

open Network

/-- §B.9 (p. 46), the recursive form of the constants (21) (0-based: `L0 l = L⁰_{l+1}`,
`L1 l = L¹_{l+1}`, `θ l = θ_{l+1}`):
`α_0 = 1`, `β_0 = 0`, `α_{l+1} = L⁰_{l+1} ‖θ_{l+1}‖_op α_l`,
`β_{l+1} = L⁰_{l+1} ‖θ_{l+1}‖_op β_l + (L¹_{l+1}/(L⁰_{l+1})²) α_{l+1}²`, which is the paper's
`β_{l+1} = (α_{l+1}/α_l) β_l + (L¹_{l+1}/(L⁰_{l+1})²) α_{l+1}²` whenever `α_l ≠ 0`; and for an
`(L+1)`-st layer with `‖θ_{L+1}‖_op = 1`, `L⁰_{L+1} = √2` and `L¹_{L+1} = 1` (the softmax layer),
`β_{L+1} = √2 β_L + α_L²`. -/
theorem alpha_beta_recursion (N : Network) (L0 L1 : ℕ → ℝ) :
    N.α L0 0 = 1 ∧ N.β L0 L1 0 = 0 ∧
    (∀ l, N.α L0 (l + 1) = L0 l * ‖N.θ l‖ * N.α L0 l) ∧
    (∀ l, N.β L0 L1 (l + 1) =
      L0 l * ‖N.θ l‖ * N.β L0 L1 l + (L1 l / (L0 l) ^ 2) * N.α L0 (l + 1) ^ 2) ∧
    (∀ l, N.α L0 l ≠ 0 → N.β L0 L1 (l + 1) =
      (N.α L0 (l + 1) / N.α L0 l) * N.β L0 L1 l + (L1 l / (L0 l) ^ 2) * N.α L0 (l + 1) ^ 2) ∧
    (∀ L, ‖N.θ L‖ = 1 → L0 L = Real.sqrt 2 → L1 L = 1 →
      N.β L0 L1 (L + 1) = Real.sqrt 2 * N.β L0 L1 L + N.α L0 L ^ 2) := by sorry

end CertDRO.NNSmooth
