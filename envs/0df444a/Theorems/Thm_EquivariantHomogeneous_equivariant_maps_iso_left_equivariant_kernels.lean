-- Prove2me | Theorems.Thm_EquivariantHomogeneous_equivariant_maps_iso_left_equivariant_kernels
-- name    : EquivariantHomogeneous.equivariant_maps_iso_left_equivariant_kernels
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:35:47.021795+00:00
-- url     : https://prove2.me/theorems/3ee67c2d-89c8-4b90-a100-4eeaf2035174
-- title:
--   Theorem 3.3: equivariant maps correspond to left-equivariant kernels on G/H₁
-- statement:
--   Let $G$ be a finite group with its counting (Haar) measure, $H_1,H_2\le G$, $s_1$ a section of $G\to G/H_1$ with $s_1(H_1)=e$, and $\rho_i$ representations of $H_i$ on finite-dimensional real vector spaces $V_i$. Let
--
--   $$\mathcal K_C=\{\overleftarrow\kappa:G/H_1\to\mathrm{Hom}(V_1,V_2)\mid\overleftarrow\kappa(h_2x)=\rho_2(h_2)\overleftarrow\kappa(x)\rho_1(\mathrm h_1(x,h_2)^{-1})\ \forall h_2\in H_2,\,x\in G/H_1\}.$$
--
--   Then $\overleftarrow\kappa\mapsto\Gamma_G(\Lambda_{\mathcal K}\overleftarrow\kappa)$ is an isomorphism from $\mathcal K_C$ onto $\mathcal H$:
--
--   1. for $\overleftarrow\kappa\in\mathcal K_C$, $f\mapsto(\Lambda_{\mathcal K}\overleftarrow\kappa)\star f$ maps Mackey functions for $\rho_1$ to Mackey functions for $\rho_2$ and commutes with the induced representations;
--   2. every equivariant linear $\Phi:\mathcal I_G^1\to\mathcal I_G^2$ equals $f\mapsto(\Lambda_{\mathcal K}\overleftarrow\kappa)\star f$ for exactly one $\overleftarrow\kappa\in\mathcal K_C$.
--
--   **Formalization Note** The group is finite, for the reason given under Theorem 3.1. The isomorphism is the composite of $\Lambda_{\mathcal K}$ (eq. (10)) with $\Gamma_G$, as in the paper's proof.
-- source:
--   Cohen, Geiger and Weiler, A General Theory of Equivariant CNNs on Homogeneous Spaces, arXiv:1811.02017v2 (NeurIPS 2019), Section 3.1, Theorem 3.3, Eqs. (9)-(11), pp. 6-7

import Mathlib
import Definitions.Def_EquivariantHomogeneous_Basic

open EquivariantHomogeneous

namespace EquivariantHomogeneous

theorem equivariant_maps_iso_left_equivariant_kernels {G : Type*} [Group G] [Fintype G] {H₁ H₂ : Subgroup G}
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
    (s₁ : CosetSection H₁) (ρ₁ : Representation ℝ H₁ V₁) (ρ₂ : Representation ℝ H₂ V₂) :
    (∀ κ ∈ kernelsC s₁ ρ₁ ρ₂,
      (∀ f ∈ mackey ρ₁, corr (liftKernel s₁ ρ₁ κ) f ∈ mackey ρ₂) ∧
      ∀ (u : G) (f : G → V₁), f ∈ mackey ρ₁ →
        corr (liftKernel s₁ ρ₁ κ) (indG u f) = indG u (corr (liftKernel s₁ ρ₁ κ) f)) ∧
    ∀ Φ ∈ equivariantMaps ρ₁ ρ₂, ∃! κ : G ⧸ H₁ → V₁ →ₗ[ℝ] V₂, κ ∈ kernelsC s₁ ρ₁ ρ₂ ∧
      ∀ f : mackey ρ₁, ((Φ f : mackey ρ₂) : G → V₂) = corr (liftKernel s₁ ρ₁ κ) (f : G → V₁) := by sorry

end EquivariantHomogeneous
