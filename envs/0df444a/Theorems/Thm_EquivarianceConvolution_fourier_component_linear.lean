-- Prove2me | Theorems.Thm_EquivarianceConvolution_fourier_component_linear
-- name    : EquivarianceConvolution.fourier_component_linear
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:02:09.384469+00:00
-- url     : https://prove2.me/theorems/ff68c5c0-c782-4162-999c-db5e9ac7c42b
-- title:
--   Lemma 7: Fourier components transform linearly under equivariant maps
-- statement:
--   Let $G$ be a finite group with subgroups $H,K$, and let $\phi:L(G/H)\to L(G/K)$ be a linear map that is equivariant with the translation actions. Fourier transforms are taken with respect to the origins $H$ and $K$. Then for each irreducible representation $\rho$ of $G$ there is a linear map $\Phi_\rho$ on $\mathbb C^{d_\rho\times d_\rho}$ such that for every $f\in L(G/H)$
--
--   $$\widehat{\phi(f)}(\rho)=\Phi_\rho\big(\hat f(\rho)\big).$$
--
--   In words, each Fourier component of the output depends linearly on the corresponding Fourier component of the input alone.
-- source:
--   Kondor and Trivedi, On the Generalization of Equivariance and Convolution in Neural Networks to the Action of Compact Groups, arXiv:1802.03690v3 (ICML 2018), Appendix E, Lemma 7, p. 13

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

open scoped BigOperators

namespace EquivarianceConvolution

theorem fourier_component_linear {G : Type*} [Group G] [Fintype G] (H K : Subgroup G)
    (φ : (G ⧸ H → ℂ) →ₗ[ℂ] (G ⧸ K → ℂ)) (hφ : IsEquivariantMap G ⇑φ) {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : IsIrrep ρ) :
    ∃ Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ,
      ∀ f : G ⧸ H → ℂ, groupFourier ρ (liftQ (φ f)) = Φ (groupFourier ρ (liftQ f)) := by sorry

end EquivarianceConvolution
