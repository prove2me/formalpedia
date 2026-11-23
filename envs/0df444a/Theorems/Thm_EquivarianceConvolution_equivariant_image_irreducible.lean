-- Prove2me | Theorems.Thm_EquivarianceConvolution_equivariant_image_irreducible
-- name    : EquivarianceConvolution.equivariant_image_irreducible
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T20:01:01.897159+00:00
-- url     : https://prove2.me/theorems/1cf1b8e3-5bd6-479d-8e7c-2106ed8ea56d
-- title:
--   Lemma 5 (as proved): equivariant maps carry irreducible subspaces to equivalent ones
-- statement:
--   Let a finite group $G$ act linearly on complex vector spaces $U$ and $V$ by $\{T_g\}$ and $\{T'_g\}$, and let $\phi:U\to V$ be a linear map with $\phi(T_gu)=T'_g\phi(u)$. Let $W\subseteq U$ be an irreducible subspace with $\phi(W)\neq0$. Then $Z=\phi(W)$ is an irreducible subspace of $V$, and the restriction of $\{T_g\}$ to $W$ is equivalent to the restriction of $\{T'_g\}$ to $Z$.
--
--   **Formalization Note** The hypothesis $\phi(W)\ne0$ is not in the printed Lemma 5, which is false without it (take $\phi=0$: then $Z=0$, which is not irreducible and not equivalent to $W\ne0$). The paper's proof uses it when it picks a nonzero vector of $Z$.
-- source:
--   Kondor and Trivedi, On the Generalization of Equivariance and Convolution in Neural Networks to the Action of Compact Groups, arXiv:1802.03690v3 (ICML 2018), Appendix E, Lemma 5, pp. 12-13

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

open scoped BigOperators

namespace EquivarianceConvolution

theorem equivariant_image_irreducible {G U V : Type*} [Group G] [Fintype G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ G U) (T' : Representation ℂ G V) (φ : U →ₗ[ℂ] V)
    (hφ : IsEquivariantLinear T T' φ) (W : Submodule ℂ U) (hW : IsIrreducibleSubspace T W)
    (hne : W.map φ ≠ ⊥) :
    IsIrreducibleSubspace T' (W.map φ) ∧ AreEquivalentSubreps T W T' (W.map φ) := by sorry

end EquivarianceConvolution
