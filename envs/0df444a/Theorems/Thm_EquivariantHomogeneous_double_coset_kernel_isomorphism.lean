-- Prove2me | Theorems.Thm_EquivariantHomogeneous_double_coset_kernel_isomorphism
-- name    : EquivariantHomogeneous.double_coset_kernel_isomorphism
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:36:18.044915+00:00
-- url     : https://prove2.me/theorems/f14544e0-e1c3-4f2c-b730-ccddb7bf49c2
-- title:
--   Appendix B.2, Eqs. (39)-(46): the isomorphism Ω_K between K_D and K_C
-- statement:
--   Let $G$ be a group, $H_1,H_2\le G$, $s_1$ a section of $G\to G/H_1$ with $s_1(H_1)=e$, $\gamma$ a choice of representatives $\gamma(x)\in x$ of the double cosets $x\in H_2\backslash G/H_1$, and $\rho_i$ representations of $H_i$ on finite-dimensional real vector spaces $V_i$. Let $\mathcal K_C$ be as in Theorem 3.3 and
--
--   $$\mathcal K_D=\{\bar\kappa:H_2\backslash G/H_1\to\mathrm{Hom}(V_1,V_2)\mid\bar\kappa(x)=\rho_2(h)\bar\kappa(x)\rho_1^x(h)^{-1}\ \forall x,\ \forall h\in H_2^{\gamma(x)H_1}\},$$
--
--   with $\rho_1^x(h)=\rho_1(\mathrm h_1(\gamma(x)H_1,h))$. Let $[\Omega_{\mathcal K}^{-1}\overleftarrow\kappa](x)=\overleftarrow\kappa(\gamma(x)H_1)$. Let $[\Omega_{\mathcal K}\bar\kappa](y)=\rho_2(h)\bar\kappa(H_2y)\rho_1(\mathrm h_1(\gamma(H_2y)H_1,h))^{-1}$, where $h\in H_2$ is any element with $y=h\gamma(H_2y)H_1$. Then:
--
--   1. $\Omega_{\mathcal K}^{-1}$ maps $\mathcal K_C$ into $\mathcal K_D$;
--   2. $\Omega_{\mathcal K}$ maps $\mathcal K_D$ into $\mathcal K_C$;
--   3. $\Omega_{\mathcal K}\Omega_{\mathcal K}^{-1}\overleftarrow\kappa=\overleftarrow\kappa$ for $\overleftarrow\kappa\in\mathcal K_C$, and $\Omega_{\mathcal K}^{-1}\Omega_{\mathcal K}\bar\kappa=\bar\kappa$ for $\bar\kappa\in\mathcal K_D$.
--
--   **Formalization Note** The element $h$ in $\Omega_{\mathcal K}$ is not unique. The definition picks one by Hilbert's $\varepsilon$, and items 2-3 are claimed for that particular choice. The statement does not assert that the result is independent of the choice, though a proof will in effect need this (the paper does not check it; it holds for $\bar\kappa\in\mathcal K_D$). The statement holds for every group.
-- source:
--   Cohen, Geiger and Weiler, A General Theory of Equivariant CNNs on Homogeneous Spaces, arXiv:1811.02017v2 (NeurIPS 2019), Appendix B.2, Eqs. (38)-(46), pp. 16-17

import Mathlib
import Definitions.Def_EquivariantHomogeneous_Basic

open EquivariantHomogeneous

namespace EquivariantHomogeneous

theorem double_coset_kernel_isomorphism {G : Type*} [Group G] {H₁ H₂ : Subgroup G}
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
    (s₁ : CosetSection H₁) (γ : DoubleCosetSection H₂ H₁)
    (ρ₁ : Representation ℝ H₁ V₁) (ρ₂ : Representation ℝ H₂ V₂) :
    (∀ κ ∈ kernelsC s₁ ρ₁ ρ₂, restrictKernel γ κ ∈ kernelsD s₁ γ ρ₁ ρ₂) ∧
    (∀ κ ∈ kernelsD s₁ γ ρ₁ ρ₂, extendKernel s₁ γ ρ₁ ρ₂ κ ∈ kernelsC s₁ ρ₁ ρ₂) ∧
    (∀ κ ∈ kernelsC s₁ ρ₁ ρ₂, extendKernel s₁ γ ρ₁ ρ₂ (restrictKernel γ κ) = κ) ∧
    (∀ κ ∈ kernelsD s₁ γ ρ₁ ρ₂, restrictKernel γ (extendKernel s₁ γ ρ₁ ρ₂ κ) = κ) := by sorry

end EquivariantHomogeneous
