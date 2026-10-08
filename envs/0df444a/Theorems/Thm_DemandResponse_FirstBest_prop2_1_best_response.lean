-- Prove2me | Theorems.Thm_DemandResponse_FirstBest_prop2_1_best_response
-- name    : DemandResponse.FirstBest.prop2_1_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:01:18.779784+00:00
-- url     : https://prove2.me/theorems/b81c1b4a-93ff-4b81-8795-01c4768683e4
-- title:
--   Proposition 2.1 — consumer's best response â(z), b̂(γ) and the closed forms of H_m, H_v (H_m corrected beyond A_max)
-- statement:
--   In the demand-response model, let $A=\prod_i[0,\mu_iA_{\max}]$, $B=[\varepsilon,1]^d$, $c_1(a)=\frac12\sum_ia_i^2/\mu_i$, $c_2(b)=\sum_j\frac{\sigma_j^2}{\lambda_j}(b_j^{-1}-1)$ and $|\sigma(b)|^2=\sum_j\sigma_j^2b_j$, and let $H_m$, $H_v$ be the Hamiltonians (2.9). Let $\hat a_i(z)=\mu_i(z^-\wedge A_{\max})$ and $\hat b_j(\gamma)=(1\wedge(\lambda_j\gamma^-)^{-1/2})\vee\varepsilon$ for $j=1,\dots,d$. Then:
--
--   1. for every $z\in\mathbb R$, $\hat a(z)\in A$ and $\hat a(z)$ minimises $a\mapsto a\cdot\mathbf 1\,z+c_1(a)$ over $A$;
--   2. for every $\gamma\in\mathbb R$, $\hat b(\gamma)\in B$ and $\hat b(\gamma)$ minimises $b\mapsto c_2(b)-\gamma|\sigma(b)|^2$ over $B$;
--   3. for every $z$, with $m:=z^-\wedge A_{\max}$,
--   $$H_m(z)=\bar\mu\Big(m\,z^--\frac{m^2}2\Big);$$
--   4. for every $\gamma$, $H_v(\gamma)=-\frac12\big(c_2(\hat b(\gamma))-\gamma|\sigma(\hat b(\gamma))|^2\big)$.
--
--   The Hamiltonian is the consumer's instantaneous benefit from a payment rate $z$ on the consumption drift and $\gamma$ on its volatility; this proposition makes it explicit, and it is what turns the first-best value into a closed form.
--
--   **Formalization Note** The paper prints $H_m(z)=\frac12\bar\mu(z^-\wedge A_{\max})^2$, which is false when $z^->A_{\max}$ (for $N=1$, $\mu=1$, $A_{\max}=1$, $z=-10$ the minimum of $-10a+a^2/2$ over $[0,1]$ is $-9.5$, so $H_m=9.5$, not $0.5$). Item 3 is the corrected formula, equal to the printed one exactly when $z^-\le A_{\max}$. The page's index range "$j=1,\dots,N$" for $\hat b$ is read as $j=1,\dots,d$. When $\gamma^-=0$ the paper reads $(\lambda_j\gamma^-)^{-1/2}$ as $+\infty$, so $\hat b_j=1$; the Lean definition makes this case explicit.
-- source:
--   arXiv:1810.09063v3, Proposition 2.1 (p. 9)

import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Hamiltonian

namespace DemandResponse.FirstBest

/-- Proposition 2.1 (consumer's best response), with the closed form of `H_m` corrected beyond
`Amax` and the index range of `b̂` read as `j = 1, …, d`. -/
theorem prop2_1_best_response {N d : ℕ} (P : Params N d) :
    (∀ z : ℝ, aHat P z ∈ effortA P ∧ ∀ a ∈ effortA P,
      (∑ i, aHat P z i) * z + c1 P (aHat P z) ≤ (∑ i, a i) * z + c1 P a) ∧
    (∀ γ : ℝ, bHat P γ ∈ effortB P ∧ ∀ b ∈ effortB P,
      c2 P (bHat P γ) - γ * sigSq P (bHat P γ) ≤ c2 P b - γ * sigSq P b) ∧
    (∀ z : ℝ, Hm P z =
      muBar P * (min (xneg z) P.Amax * xneg z - min (xneg z) P.Amax ^ 2 / 2)) ∧
    (∀ γ : ℝ, Hv P γ = -(1 / 2) * (c2 P (bHat P γ) - γ * sigSq P (bHat P γ))) := by sorry

end DemandResponse.FirstBest
