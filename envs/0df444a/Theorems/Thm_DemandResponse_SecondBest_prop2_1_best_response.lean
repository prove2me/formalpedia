-- Prove2me | Theorems.Thm_DemandResponse_SecondBest_prop2_1_best_response
-- name    : DemandResponse.SecondBest.prop2_1_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T03:42:07.902231+00:00
-- url     : https://prove2.me/theorems/6423c88f-0e19-420c-9b52-80b94aaea533
-- title:
--   Proposition 2.1 — consumer's best response $\hat a(z)$, $\hat b(\gamma)$ and the closed forms of $H_m$, $H_v$ ($H_m$ corrected beyond $A_{\max}$)
-- statement:
--   In the demand-response model with effort boxes $A=\prod_i[0,\mu_iA_{\max}]$ and $B=[\varepsilon,1]^d$, costs $c_1,c_2$ and Hamiltonians $H_m,H_v$ defined by the infima (2.9), the consumer's best response to the payment rates $(z,\gamma)$ is $\hat a_i(z)=\mu_i(z^-\wedge A_{\max})$ and $\hat b_j(\gamma)=(1\wedge(\lambda_j\gamma^-)^{-1/2})\vee\varepsilon$. Precisely:
--
--   1. for every $z\in\mathbb R$, $\hat a(z)\in A$ and $\hat a(z)$ minimises $a\mapsto a\cdot\mathbf 1\,z+c_1(a)$ over $A$;
--   2. for every $\gamma\in\mathbb R$, $\hat b(\gamma)\in B$ and $\hat b(\gamma)$ minimises $b\mapsto c_2(b)-\gamma|\sigma(b)|^2$ over $B$;
--   3. for every $z$, with $m:=z^-\wedge A_{\max}$,
--   $$H_m(z)=\bar\mu\Big(m\,z^--\frac{m^2}2\Big);$$
--   4. for every $\gamma$,
--   $$H_v(\gamma)=-\frac12\Big(\hat c_2(\gamma)-\gamma|\hat\sigma(\gamma)|^2\Big).$$
--
--   The closed forms of the consumer's Hamiltonian are what makes the producer's problem a deterministic scalar optimisation in the payment rates.
--
--   **Formalization Note.** The paper prints $H_m(z)=\frac12\bar\mu(z^-\wedge A_{\max})^2$, which is false when $z^->A_{\max}$ (for $N=1$, $\mu=1$, $A_{\max}=1$, $z=-10$ the minimum of $-10a+a^2/2$ over $[0,1]$ is $-9.5$, so $H_m=9.5$, not $0.5$). Item 3 is the corrected formula; it equals the printed one exactly when $z^-\le A_{\max}$. The page's index range "$j=1,\dots,N$" for $\hat b$ is read as $j=1,\dots,d$. $\hat b_j(\gamma)$ is $1$ when $\lambda_j\gamma^-\le1$, the paper's reading of $0^{-1/2}=+\infty$.
-- source:
--   arXiv:1810.09063v3, Proposition 2.1 (p. 9)

import Mathlib
import Definitions.Def_DemandResponse_SecondBest_Hamiltonian

namespace DemandResponse.SecondBest

/-- Proposition 2.1 (arXiv:1810.09063v3, p. 9), with the closed form of `H_m` corrected beyond `A_max`
and the index range of `b̂` read as `j = 1, …, d`. -/
theorem prop2_1_best_response {N d : ℕ} (P : Params N d) :
    (∀ z : ℝ, ahat P z ∈ EffA P ∧
      ∀ a ∈ EffA P, (∑ i, ahat P z i) * z + c1 P (ahat P z) ≤ (∑ i, a i) * z + c1 P a) ∧
    (∀ γ : ℝ, bhat P γ ∈ EffB P ∧
      ∀ b ∈ EffB P, c2 P (bhat P γ) - γ * sigmaSq P (bhat P γ) ≤ c2 P b - γ * sigmaSq P b) ∧
    (∀ z : ℝ, Hm P z =
      muBar P * (min (negp z) P.Amax * negp z - min (negp z) P.Amax ^ 2 / 2)) ∧
    (∀ γ : ℝ, Hv P γ = -(1 / 2) * (c2hat P γ - γ * sigmaHatSq P γ)) := by sorry

end DemandResponse.SecondBest
