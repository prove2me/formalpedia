-- Prove2me | Theorems.Thm_EquivarianceConvolution_equivariant_maps_isotypic
-- name    : EquivarianceConvolution.equivariant_maps_isotypic
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:01:39.641198+00:00
-- url     : https://prove2.me/theorems/e61578fa-1161-4746-8a5b-373fa96549a4
-- title:
--   Lemma 6: equivariant maps respect isotypic decompositions
-- statement:
--   Let a finite group $G$ act linearly on complex vector spaces $U$ and $V$, and let $\phi:U\to V$ be a linear map equivariant with the two actions. For every irreducible representation $\rho$ of $G$, let $U_\rho$ and $V_\rho$ be the isotypic components of $U$ and $V$ belonging to $\rho$. Then
--
--   $$\phi(U_\rho)\subseteq V_\rho.$$
--
--   So an equivariant map respects the isotypic decompositions $U=\bigoplus_iU_i$ and $V=\bigoplus_iV_i$.
-- source:
--   Kondor and Trivedi, On the Generalization of Equivariance and Convolution in Neural Networks to the Action of Compact Groups, arXiv:1802.03690v3 (ICML 2018), Appendix E, Lemma 6, p. 13

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

open scoped BigOperators

namespace EquivarianceConvolution

theorem equivariant_maps_isotypic {G U V : Type*} [Group G] [Fintype G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ G U) (T' : Representation ℂ G V) (φ : U →ₗ[ℂ] V)
    (hφ : IsEquivariantLinear T T' φ) {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : IsIrrep ρ) :
    (isotypicPart T ρ).map φ ≤ isotypicPart T' ρ := by sorry

end EquivarianceConvolution
