-- Prove2me | Theorems.Thm_EquivarianceConvolution_convolution_theorem
-- name    : EquivarianceConvolution.convolution_theorem
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T20:00:32.081668+00:00
-- url     : https://prove2.me/theorems/336a2e37-3f53-4691-96ae-0d2ccf78d847
-- title:
--   Proposition 2: convolution theorem on groups
-- statement:
--   Let $G$ be a finite group and $\rho$ an irreducible representation of $G$. For all $f,g:G\to\mathbb C$, with $(f*g)(u)=\sum_{v\in G}f(uv^{-1})g(v)$,
--
--   $$\widehat{f*g}(\rho)=\hat f(\rho)\,\hat g(\rho).$$
--
--   The convolution theorem turns a convolution layer into a matrix product in each Fourier component.
--
--   **Formalization Note** The paper states the identity for $f,g$ on $G$, $G/H$, $H\backslash G$ or $H\backslash G/K$ in any combination. In each case the convolution (Definition 4, eq. (8), and its reduced forms (9), (11), (12)) and the Fourier transform are defined through the lifts of $f$ and $g$ to $G$, so the statement for arbitrary functions on $G$ covers all combinations. The group is finite (see the definitions).
-- source:
--   Kondor and Trivedi, On the Generalization of Equivariance and Convolution in Neural Networks to the Action of Compact Groups, arXiv:1802.03690v3 (ICML 2018), Section 4.2, Proposition 2, eq. (14), p. 6; proof in Appendix D, p. 12

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

open scoped BigOperators

namespace EquivarianceConvolution

theorem convolution_theorem {G : Type*} [Group G] [Fintype G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : IsIrrep ρ) (f g : G → ℂ) :
    groupFourier ρ (groupConv f g) = groupFourier ρ f * groupFourier ρ g := by sorry

end EquivarianceConvolution
