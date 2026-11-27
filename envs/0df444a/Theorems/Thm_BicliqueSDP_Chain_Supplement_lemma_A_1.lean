-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_Supplement_lemma_A_1
-- name    : BicliqueSDP.Chain.Supplement.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:18:44.26394+00:00
-- url     : https://prove2.me/theorems/9fba14b3-4342-4943-91a8-8ca5ba188f40
-- title:
--   Lemma A.1 — the second Cayley adjacency eigenvalue bound
-- statement:
--   Let $\Gamma$ be a finite group of order $n$, let $k$ be the least dimension of a nontrivial finite-dimensional complex representation, and let $A\subseteq\Gamma$ be product-free. Let $\lambda_2$ be the second largest eigenvalue, counted with multiplicity, of the full adjacency matrix of the bipartite graph joining $u$ on the left to $v$ on the right when $uv\in A$. Then
--
--   $$\lambda_2\le\sqrt{\frac{|A|(n-|A|)}{k}}.$$
--
--   This is the spectral support for the sharpened product-free density bound in Theorem A.2.
--
--   **Formalization Note** The representation minimum is a least-element hypothesis. The trivial group has no such $k$, and its only product-free set is empty. The second adjacency eigenvalue itself is still defined for that group.
--
--   Differences from the source:
--   - encoding: The source denotes the minimum nontrivial representation dimension by k and orders eigenvalues with multiplicity → Lean requires IsLeast of the dimensions of nontrivial complex representations, and takes index 1 of the ordered Hermitian eigenvalue list; reason: This gives the stated minimum its literal meaning without a junk default for the trivial group, and keeps the full 2n by 2n spectrum.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, pp. 35–36, Lemma A.1, Eq. (82)

import Definitions.Def_BicliqueSDP_Chain_Supplement_ProductFree
set_option autoImplicit false

namespace BicliqueSDP.Chain.Supplement

/-- Lemma A.1, including the exact factor n-|A| and the full adjacency spectrum. -/
theorem lemma_A_1 {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ) (k : ℕ) (hk : IsMinRepDim Γ k) (hA : IsProductFree A) :
    lambda2 A ≤ Real.sqrt ((A.card : ℝ) * ((Fintype.card Γ : ℝ) - A.card) / k) := by sorry

end BicliqueSDP.Chain.Supplement
