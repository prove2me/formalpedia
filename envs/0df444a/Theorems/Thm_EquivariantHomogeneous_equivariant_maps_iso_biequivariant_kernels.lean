-- Prove2me | Theorems.Thm_EquivariantHomogeneous_equivariant_maps_iso_biequivariant_kernels
-- name    : EquivariantHomogeneous.equivariant_maps_iso_biequivariant_kernels
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:35:01.110583+00:00
-- url     : https://prove2.me/theorems/63dce492-40ff-414e-b1f0-f33bdf80df26
-- title:
--   Theorem 3.2: equivariant maps correspond to bi-equivariant kernels on G
-- statement:
--   Let $G$ be a finite group with its counting (Haar) measure, $H_1,H_2\le G$, and $\rho_i$ representations of $H_i$ on finite-dimensional real vector spaces $V_i$. Let
--
--   $$\mathcal K_G=\{\kappa:G\to\mathrm{Hom}(V_1,V_2)\mid \kappa(h_2gh_1)=\rho_2(h_2)\kappa(g)\rho_1(h_1)\ \forall g\in G,\,h_1\in H_1,\,h_2\in H_2\}.$$
--
--   Then $\Gamma_G:\kappa\mapsto(f\mapsto\kappa\star f)$ is an isomorphism from $\mathcal K_G$ onto $\mathcal H=\mathrm{Hom}_G(\mathcal I^1,\mathcal I^2)$:
--
--   1. for every $\kappa\in\mathcal K_G$, $\kappa\star f$ is a Mackey function for $\rho_2$ whenever $f$ is one for $\rho_1$, and $\kappa\star\pi_1(u)f=\pi_2(u)(\kappa\star f)$ for all $u\in G$;
--   2. for every equivariant linear $\Phi:\mathcal I_G^1\to\mathcal I_G^2$ there is exactly one $\kappa\in\mathcal K_G$ with $\Phi f=\kappa\star f$ for all $f\in\mathcal I_G^1$.
--
--   This is the paper's main correspondence: equivariant linear layers are exactly correlations with bi-equivariant kernels.
--
--   **Formalization Note** As for Theorem 3.1, the group is finite and integrals are sums. "Isomorphic" is stated as: $\Gamma_G$ is well defined into $\mathcal H$ and bijective. $\Gamma_G$ is linear in $\kappa$, so this is a linear isomorphism.
-- source:
--   Cohen, Geiger and Weiler, A General Theory of Equivariant CNNs on Homogeneous Spaces, arXiv:1811.02017v2 (NeurIPS 2019), Section 3.1, Theorem 3.2, Eq. (8), p. 6; proof in Appendix B.1, Eqs. (35)-(37), p. 16

import Mathlib
import Definitions.Def_EquivariantHomogeneous_Basic

open EquivariantHomogeneous

namespace EquivariantHomogeneous

theorem equivariant_maps_iso_biequivariant_kernels {G : Type*} [Group G] [Fintype G] {H₁ H₂ : Subgroup G}
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
    (ρ₁ : Representation ℝ H₁ V₁) (ρ₂ : Representation ℝ H₂ V₂) :
    (∀ κ ∈ kernelsG ρ₁ ρ₂,
      (∀ f ∈ mackey ρ₁, corr κ f ∈ mackey ρ₂) ∧
      ∀ (u : G) (f : G → V₁), f ∈ mackey ρ₁ → corr κ (indG u f) = indG u (corr κ f)) ∧
    ∀ Φ ∈ equivariantMaps ρ₁ ρ₂, ∃! κ : G → V₁ →ₗ[ℝ] V₂, κ ∈ kernelsG ρ₁ ρ₂ ∧
      ∀ f : mackey ρ₁, ((Φ f : mackey ρ₂) : G → V₂) = corr κ (f : G → V₁) := by sorry

end EquivariantHomogeneous
