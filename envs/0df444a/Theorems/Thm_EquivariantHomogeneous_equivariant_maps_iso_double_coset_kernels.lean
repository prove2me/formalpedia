-- Prove2me | Theorems.Thm_EquivariantHomogeneous_equivariant_maps_iso_double_coset_kernels
-- name    : EquivariantHomogeneous.equivariant_maps_iso_double_coset_kernels
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:36:56.965879+00:00
-- url     : https://prove2.me/theorems/95ebe7c4-8bb5-4d19-b7fa-37f7e9f6c4c5
-- title:
--   Theorem 3.4: equivariant maps correspond to stabilizer-equivariant kernels on H₂\G/H₁
-- statement:
--   Let $G$ be a finite group with its counting (Haar) measure, and let $H_1,H_2,s_1,\gamma,\rho_1,\rho_2$ and $\mathcal K_D$ be as above, with $V_1,V_2$ finite-dimensional real vector spaces. Then:
--
--   1. for each double coset $x$, $\rho_1^x(h)=\rho_1(\mathrm h_1(\gamma(x)H_1,h))$ is a representation of the stabilizer $H_2^{\gamma(x)H_1}=\{h\in H_2\mid h\gamma(x)H_1=\gamma(x)H_1\}$: $\rho_1^x(hk)=\rho_1^x(h)\rho_1^x(k)$ for $h,k$ in the stabilizer, and $\rho_1^x(e)=\mathrm{id}$;
--   2. for $\bar\kappa\in\mathcal K_D$, $f\mapsto(\Lambda_{\mathcal K}\Omega_{\mathcal K}\bar\kappa)\star f$ is an equivariant linear map $\mathcal I_G^1\to\mathcal I_G^2$;
--   3. every equivariant linear $\Phi:\mathcal I_G^1\to\mathcal I_G^2$ equals $f\mapsto(\Lambda_{\mathcal K}\Omega_{\mathcal K}\bar\kappa)\star f$ for exactly one $\bar\kappa\in\mathcal K_D$.
--
--   So $\mathcal H\cong\mathcal K_D$: an equivariant kernel is a matrix-valued function on the double coset space, constrained only on stabilizers.
--
--   **Formalization Note** The group is finite, for the reason given under Theorem 3.1. Eq. (13) also asserts $\rho_1(\mathrm h_1(\gamma(x)H_1,h))=\rho_1(\gamma(x)^{-1}h\gamma(x))$. That holds only when $s_1(\gamma(x)H_1)=\gamma(x)$, so the first expression, which is the one the proof uses, is the definition. The paper writes the stabilizer as "$\le H_1$"; it is a subgroup of $H_2$.
-- source:
--   Cohen, Geiger and Weiler, A General Theory of Equivariant CNNs on Homogeneous Spaces, arXiv:1811.02017v2 (NeurIPS 2019), Section 3.1, Theorem 3.4, Eqs. (12)-(13), p. 7; proof in Appendix B.2, Eqs. (38)-(46), pp. 16-17

import Mathlib
import Definitions.Def_EquivariantHomogeneous_Basic

open EquivariantHomogeneous

namespace EquivariantHomogeneous

theorem equivariant_maps_iso_double_coset_kernels {G : Type*} [Group G] [Fintype G] {H₁ H₂ : Subgroup G}
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
    (s₁ : CosetSection H₁) (γ : DoubleCosetSection H₂ H₁)
    (ρ₁ : Representation ℝ H₁ V₁) (ρ₂ : Representation ℝ H₂ V₂) :
    (∀ (x : DoubleCoset.Quotient (H₂ : Set G) (H₁ : Set G)) (h k : H₂),
      (h : G) • (QuotientGroup.mk (γ.toFun x) : G ⧸ H₁) = QuotientGroup.mk (γ.toFun x) →
      (k : G) • (QuotientGroup.mk (γ.toFun x) : G ⧸ H₁) = QuotientGroup.mk (γ.toFun x) →
      rhoStab s₁ γ ρ₁ x ((h : G) * k) = (rhoStab s₁ γ ρ₁ x h).comp (rhoStab s₁ γ ρ₁ x k)) ∧
    (∀ x : DoubleCoset.Quotient (H₂ : Set G) (H₁ : Set G), rhoStab s₁ γ ρ₁ x 1 = LinearMap.id) ∧
    (∀ κ ∈ kernelsD s₁ γ ρ₁ ρ₂,
      (∀ f ∈ mackey ρ₁, corr (liftKernel s₁ ρ₁ (extendKernel s₁ γ ρ₁ ρ₂ κ)) f ∈ mackey ρ₂) ∧
      ∀ (u : G) (f : G → V₁), f ∈ mackey ρ₁ →
        corr (liftKernel s₁ ρ₁ (extendKernel s₁ γ ρ₁ ρ₂ κ)) (indG u f) =
          indG u (corr (liftKernel s₁ ρ₁ (extendKernel s₁ γ ρ₁ ρ₂ κ)) f)) ∧
    ∀ Φ ∈ equivariantMaps ρ₁ ρ₂,
      ∃! κ : DoubleCoset.Quotient (H₂ : Set G) (H₁ : Set G) → V₁ →ₗ[ℝ] V₂,
        κ ∈ kernelsD s₁ γ ρ₁ ρ₂ ∧
        ∀ f : mackey ρ₁, ((Φ f : mackey ρ₂) : G → V₂) =
          corr (liftKernel s₁ ρ₁ (extendKernel s₁ γ ρ₁ ρ₂ κ)) (f : G → V₁) := by sorry

end EquivariantHomogeneous
