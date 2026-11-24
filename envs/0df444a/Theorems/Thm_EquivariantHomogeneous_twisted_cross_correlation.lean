-- Prove2me | Theorems.Thm_EquivariantHomogeneous_twisted_cross_correlation
-- name    : EquivariantHomogeneous.twisted_cross_correlation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:37:28.342421+00:00
-- url     : https://prove2.me/theorems/519d99d8-e0d1-41ee-85e2-31a7584f7fb6
-- title:
--   Section 3.2, Eq. (14): the ρ₁-twisted cross-correlation on G/H₁
-- statement:
--   Let $G$ be a finite group with its counting (Haar) measure, $H_1,H_2\le G$ with sections $s_1,s_2$ normalised by $s_i(H_i)=e$, $\rho_i$ representations of $H_i$ on finite-dimensional real vector spaces $V_i$, $\overleftarrow\kappa\in\mathcal K_C$, and $\kappa=\Lambda_{\mathcal K}\overleftarrow\kappa$. Then for every $f:G/H_1\to V_1$ and $x\in G/H_2$,
--
--   $$[\Lambda_2^{-1}[\kappa\star[\Lambda_1f]]](x)=\int_{G/H_1}\kappa(s_2(x)^{-1}s_1(y))f(y)\,dy=\int_{G/H_1}\overleftarrow\kappa(s_2(x)^{-1}y)\,\rho_1\big(\mathrm h_1(s_2(x)^{-1}s_1(y))\big)f(y)\,dy,$$
--
--   where $\int_{G/H_1}F(y)\,dy=\sum_{g\in G}F(gH_1)$ (eq. (34)).
--
--   This is the $\rho_1$-twisted cross-correlation on $G/H_1$, the form in which G-CNN layers on fields over $G/H_1$ are implemented.
--
--   **Formalization Note** The paper writes the first integral over $G$. Since $y$ is a point of $G/H_1$, it is read as the integral over $G/H_1$ in the paper's sense (eq. (34)), and with that reading the identity holds exactly.
-- source:
--   Cohen, Geiger and Weiler, A General Theory of Equivariant CNNs on Homogeneous Spaces, arXiv:1811.02017v2 (NeurIPS 2019), Section 3.2, Eq. (14), p. 7

import Mathlib
import Definitions.Def_EquivariantHomogeneous_Basic

open EquivariantHomogeneous

namespace EquivariantHomogeneous

theorem twisted_cross_correlation {G : Type*} [Group G] [Fintype G] {H₁ H₂ : Subgroup G}
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
    (s₁ : CosetSection H₁) (s₂ : CosetSection H₂)
    (ρ₁ : Representation ℝ H₁ V₁) (ρ₂ : Representation ℝ H₂ V₂)
    (κ : G ⧸ H₁ → V₁ →ₗ[ℝ] V₂) (hκ : κ ∈ kernelsC s₁ ρ₁ ρ₂)
    (f : G ⧸ H₁ → V₁) (x : G ⧸ H₂) :
    unliftSection s₂ (corr (liftKernel s₁ ρ₁ κ) (liftSection s₁ ρ₁ f)) x =
        quotientIntegral H₁ (fun y => liftKernel s₁ ρ₁ κ ((s₂.toFun x)⁻¹ * s₁.toFun y) (f y)) ∧
    unliftSection s₂ (corr (liftKernel s₁ ρ₁ κ) (liftSection s₁ ρ₁ f)) x =
        quotientIntegral H₁ (fun y =>
          κ ((s₂.toFun x)⁻¹ • y) (ρ₁ (hElem s₁ ((s₂.toFun x)⁻¹ * s₁.toFun y)) (f y))) := by sorry

end EquivariantHomogeneous
