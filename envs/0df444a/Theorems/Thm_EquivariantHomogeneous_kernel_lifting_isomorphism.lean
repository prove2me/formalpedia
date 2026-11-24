-- Prove2me | Theorems.Thm_EquivariantHomogeneous_kernel_lifting_isomorphism
-- name    : EquivariantHomogeneous.kernel_lifting_isomorphism
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:35:26.813292+00:00
-- url     : https://prove2.me/theorems/c036850e-57a2-4a8a-aca0-82a35ea453e4
-- title:
--   Theorem 3.3 (proof), Eqs. (10)-(11): the kernel lifting isomorphism between K_C and K_G
-- statement:
--   Let $G$ be a group, $H_1,H_2\le G$, $s_1$ a section of $G\to G/H_1$ with $s_1(H_1)=e$, $\mathrm h_1$ its $\mathrm h$-function, and $\rho_i$ representations of $H_i$ on finite-dimensional real vector spaces $V_i$. For $\overleftarrow\kappa:G/H_1\to\mathrm{Hom}(V_1,V_2)$ put $[\Lambda_{\mathcal K}\overleftarrow\kappa](g)=\overleftarrow\kappa(gH_1)\rho_1(\mathrm h_1(g))$ (eq. (10)). Then:
--
--   1. $\Lambda_{\mathcal K}\overleftarrow\kappa$ is right $H_1$-equivariant, $[\Lambda_{\mathcal K}\overleftarrow\kappa](gh_1)=[\Lambda_{\mathcal K}\overleftarrow\kappa](g)\rho_1(h_1)$, for every $\overleftarrow\kappa$;
--   2. (eq. (11)) $\Lambda_{\mathcal K}\overleftarrow\kappa$ is left $H_2$-equivariant, $\kappa(h_2g)=\rho_2(h_2)\kappa(g)$, if and only if
--   $$\overleftarrow\kappa(h_2x)=\rho_2(h_2)\,\overleftarrow\kappa(x)\,\rho_1(\mathrm h_1(x,h_2)^{-1})\quad\forall h_2\in H_2,\ x\in G/H_1,$$
--   i.e. iff $\overleftarrow\kappa\in\mathcal K_C$;
--   3. $\Lambda_{\mathcal K}$ maps $\mathcal K_C$ into $\mathcal K_G$, and $\kappa\mapsto\kappa\circ s_1$ maps $\mathcal K_G$ into $\mathcal K_C$;
--   4. these two maps are mutually inverse on $\mathcal K_C$ and $\mathcal K_G$.
--
--   **Formalization Note** This is the content of the proof of Theorem 3.3. It holds for every group, so no finiteness is assumed.
-- source:
--   Cohen, Geiger and Weiler, A General Theory of Equivariant CNNs on Homogeneous Spaces, arXiv:1811.02017v2 (NeurIPS 2019), Section 3.1, proof of Theorem 3.3, Eqs. (10)-(11), p. 7

import Mathlib
import Definitions.Def_EquivariantHomogeneous_Basic

open EquivariantHomogeneous

namespace EquivariantHomogeneous

theorem kernel_lifting_isomorphism {G : Type*} [Group G] {H₁ H₂ : Subgroup G}
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
    (s₁ : CosetSection H₁) (ρ₁ : Representation ℝ H₁ V₁) (ρ₂ : Representation ℝ H₂ V₂) :
    (∀ (κ : G ⧸ H₁ → V₁ →ₗ[ℝ] V₂) (g : G) (h₁ : H₁),
      liftKernel s₁ ρ₁ κ (g * (h₁ : G)) = (liftKernel s₁ ρ₁ κ g).comp (ρ₁ h₁)) ∧
    (∀ κ : G ⧸ H₁ → V₁ →ₗ[ℝ] V₂,
      (∀ (g : G) (h₂ : H₂),
        liftKernel s₁ ρ₁ κ ((h₂ : G) * g) = (ρ₂ h₂).comp (liftKernel s₁ ρ₁ κ g)) ↔
      κ ∈ kernelsC s₁ ρ₁ ρ₂) ∧
    (∀ κ ∈ kernelsC s₁ ρ₁ ρ₂, liftKernel s₁ ρ₁ κ ∈ kernelsG ρ₁ ρ₂) ∧
    (∀ κ ∈ kernelsG ρ₁ ρ₂, (fun x => κ (s₁.toFun x)) ∈ kernelsC s₁ ρ₁ ρ₂) ∧
    (∀ κ ∈ kernelsC s₁ ρ₁ ρ₂, (fun x => liftKernel s₁ ρ₁ κ (s₁.toFun x)) = κ) ∧
    (∀ κ ∈ kernelsG ρ₁ ρ₂, liftKernel s₁ ρ₁ (fun x => κ (s₁.toFun x)) = κ) := by sorry

end EquivariantHomogeneous
