-- Prove2me | Theorems.Thm_EquivarianceConvolution_irrep_sum_eq_zero
-- name    : EquivarianceConvolution.irrep_sum_eq_zero
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:58:57.011397+00:00
-- url     : https://prove2.me/theorems/d54ead88-7845-4b22-94da-d6e6ca0a0775
-- title:
--   Lemma 2: the sum of a non-trivial irrep over the group vanishes
-- statement:
--   Let $G$ be a finite group and $\rho:G\to\mathbb C^{n\times n}$ an irreducible representation of $G$. If $\rho$ is not the trivial representation $\rho_{\mathrm{tr}}(u)=(1)$, then
--
--   $$\sum_{u\in G}\rho(u)=0.$$
--
--   This is the vanishing step behind the sparsity patterns of Proposition 1.
--
--   **Formalization Note** The paper states the lemma for a countable group; for an infinite group the sum is not defined, and the statement is made for finite $G$.
-- source:
--   Kondor and Trivedi, On the Generalization of Equivariance and Convolution in Neural Networks to the Action of Compact Groups, arXiv:1802.03690v3 (ICML 2018), Appendix C, Lemma 2, p. 11

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

open scoped BigOperators

namespace EquivarianceConvolution

theorem irrep_sum_eq_zero {G : Type*} [Group G] [Fintype G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : IsIrrep ρ) (htr : ¬ IsTrivialRep ρ) :
    ∑ u, ρ u = 0 := by sorry

end EquivarianceConvolution
