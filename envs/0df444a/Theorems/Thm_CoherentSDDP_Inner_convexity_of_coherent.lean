-- Prove2me | Theorems.Thm_CoherentSDDP_Inner_convexity_of_coherent
-- name    : CoherentSDDP.Inner.convexity_of_coherent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:12.784997+00:00
-- url     : https://prove2.me/theorems/143f235d-fd07-40a3-8d62-8e4fad409bcf
-- title:
--   Convexity, §2, p. 3 — subadditivity and positive homogeneity imply convexity of ρ
-- statement:
--   Let $\Omega$ be a set and let $\rho$ map real random variables $Z:\Omega\to\mathbb R$ to $\mathbb R$. Suppose $\rho$ is subadditive, $\rho(Z_1+Z_2)\le\rho(Z_1)+\rho(Z_2)$, and positively homogeneous, $\rho(\lambda Z)=\lambda\rho(Z)$ for $\lambda>0$. Then $\rho$ is convex: for all $Z_1,Z_2$ and every $\alpha\in[0,1]$,
--   $$
--   \rho\big(\alpha Z_1+(1-\alpha)Z_2\big)\le\alpha\,\rho(Z_1)+(1-\alpha)\,\rho(Z_2).
--   $$
--
--   In the paper, convexity together with monotonicity is what keeps the nested problems (1)–(2) convex, and it is the property of $\rho_t$ used in the base case of the proof of Proposition 5.
--
--   **Formalization Note** Only the two axioms named on the page are assumed. At $\alpha\in\{0,1\}$ both sides coincide, so positive homogeneity is not needed at $0$.
-- source:
--   Philpott, de Matos & Finardi, On Solving Multistage Stochastic Programs with Coherent Risk Measures, authors' manuscript of 13 August 2012 (Operations Research, 2013), p. 3, §2, Convexity

import Mathlib
import Definitions.Def_CoherentSDDP_Inner_Basic

namespace CoherentSDDP.Inner

theorem convexity_of_coherent {Ω : Type*} (ρ : (Ω → ℝ) → ℝ) (hsub : RiskSubadditive ρ)
    (hhom : RiskPosHomogeneous ρ) :
    ∀ (Z₁ Z₂ : Ω → ℝ) (α : ℝ), 0 ≤ α → α ≤ 1 →
      ρ (α • Z₁ + (1 - α) • Z₂) ≤ α * ρ Z₁ + (1 - α) * ρ Z₂ := by sorry

end CoherentSDDP.Inner
