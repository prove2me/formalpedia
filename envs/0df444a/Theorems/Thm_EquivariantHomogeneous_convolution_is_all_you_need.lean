-- Prove2me | Theorems.Thm_EquivariantHomogeneous_convolution_is_all_you_need
-- name    : EquivariantHomogeneous.convolution_is_all_you_need
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:34:24.130653+00:00
-- url     : https://prove2.me/theorems/574dc5d3-81b5-4c9a-8825-22dade8838b6
-- title:
--   Theorem 3.1: convolution is all you need
-- statement:
--   Let $G$ be a finite group with its counting (Haar) measure, and let $H_1,H_2\le G$ carry representations $\rho_i$ on finite-dimensional real vector spaces $V_i$. Let $\Phi:\mathcal I_G^1\to\mathcal I_G^2$ be a linear map between the spaces of Mackey functions that is equivariant: $\Phi\,\pi_1(u)=\pi_2(u)\,\Phi$ for all $u\in G$. Then there is a kernel $\kappa:G\to\mathrm{Hom}(V_1,V_2)$ such that
--
--   $$[\Phi f](g)=\sum_{g'\in G}\kappa(g^{-1}g')\,f(g')=[\kappa\star f](g)$$
--
--   for every Mackey function $f\in\mathcal I_G^1$ and every $g\in G$.
--
--   In words, every equivariant linear layer between field spaces is a cross-correlation with a one-argument kernel.
--
--   **Formalization Note** The paper states the theorem for locally compact unimodular groups with Haar integrals, and its proof assumes that every bounded operator has an integral kernel (eq. (5)). That fails for non-discrete groups: the identity of $L^2(\mathbb R)$ is equivariant but has no function kernel. The statement is therefore made for finite groups, where integrals are finite sums and every linear operator has a kernel.
-- source:
--   Cohen, Geiger and Weiler, A General Theory of Equivariant CNNs on Homogeneous Spaces, arXiv:1811.02017v2 (NeurIPS 2019), Section 3, Theorem 3.1, Eqs. (5)-(7), pp. 5-6

import Mathlib
import Definitions.Def_EquivariantHomogeneous_Basic

open EquivariantHomogeneous

namespace EquivariantHomogeneous

theorem convolution_is_all_you_need {G : Type*} [Group G] [Fintype G] {H₁ H₂ : Subgroup G}
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
    (ρ₁ : Representation ℝ H₁ V₁) (ρ₂ : Representation ℝ H₂ V₂)
    (Φ : mackey ρ₁ →ₗ[ℝ] mackey ρ₂) (hΦ : Φ ∈ equivariantMaps ρ₁ ρ₂) :
    ∃ κ : G → V₁ →ₗ[ℝ] V₂,
      ∀ f : mackey ρ₁, ((Φ f : mackey ρ₂) : G → V₂) = corr κ (f : G → V₁) := by sorry

end EquivariantHomogeneous
