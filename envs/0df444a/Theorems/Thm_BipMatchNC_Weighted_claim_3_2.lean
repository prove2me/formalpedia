-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_claim_3_2
-- name    : BipMatchNC.Weighted.claim_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:14:53.576093+00:00
-- url     : https://prove2.me/theorems/e114569d-f928-43ca-9ee6-154ea35faeac
-- title:
--   Claim 3.2: the nonzero blocks of any left kernel vector of the matching matrix M(G) are linearly independent polynomials
-- statement:
--   Let $F$ be a field and $G$ a balanced bipartite graph on $[n]+[n]$. Let $\gamma\in F$ have order at least $nr$, let $\alpha_1,\dots,\alpha_{n^2}\in F$ be such that the $n^2r$ elements $\alpha_j\gamma^\ell$ ($1\le j\le n^2$, $0\le\ell\le r-1$) are distinct, let $\delta\ge n$, $r>n^2\delta$ and $D=n(r-\delta)$, and let $M(G)$ be the $nD\times n^2r$ matching matrix. Let $p\in F^{nD}$ satisfy $p^TM(G)=0$, split $p=(p_1,\dots,p_n)$ into blocks $p_i\in F^D$, and view each block as the polynomial $p_i(x)=\sum_{k=0}^{D-1}p_{i,k}x^k$. Then the polynomials
--   $$\{\,p_i(x) : p_i\neq0\,\}$$
--   (the nonzero blocks, as a family indexed by $i$) are linearly independent over $F$.
--
--   This is the key step of the "full rank $\Rightarrow$ perfect matching" direction of Theorem 3.1: the independence lets the folded roots coming from the extension columns and from the edges be counted against Lemma 2.6.
--
--   Differences from the source:
--   - encoding: p ∈ F^{nD} with p^T M(G) = 0; WLOG p_1, …, p_s are the nonzero blocks → every p : Fin n × Fin D → F with Matrix.vecMul p M(G) = 0, and the family of block polynomials indexed by {i // ∃ k, p (i, k) ≠ 0}; reason: the WLOG reordering is not part of the claim; the set of nonzero blocks is the same
--   - encoding: each p_i as the coefficient vector of a polynomial p_i(x) of degree D − 1 → blockPoly p i = Σ_{k < D} p (i, k) X^k; reason: coefficient k of p_i(x) is entry k of block i, as in the proof (p^T V(α) = 0 says α is an r-folded root)
--   - encoding: §3.1 parameters: γ ∈ F of order at least nr; α_1, …, α_{n²} with the n²r elements α_jγ^ℓ (0 ≤ ℓ ≤ r − 1) distinct; δ ≥ n and r > n²δ; D = n(r − δ) → hypotheses OrderAtLeast γ (n * r), injectivity of (j, ℓ) ↦ α j * γ ^ ℓ on Fin (n * n) × Fin r, n ≤ δ, n ^ 2 * δ < r, and D written as n * (r - δ); reason: the standing assumptions of §3.1 (p. 9), stated as binders; F is an arbitrary field; under these hypotheses r > δ whenever n ≥ 1, so the ℕ-subtraction in D never truncates
--   - encoding: vertices u_1, …, u_n, v_1, …, v_n and column blocks 1, …, n² (1-based) → Fin n and Fin (n * n), 0-based; G as its bi-adjacency matrix BipGraph n; reason: indexing convention only
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), pp. 10–11 (PDF 11–12), Claim 3.2 with the setup of the proof of Theorem 3.1

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Folded
import Definitions.Def_BipMatchNC_Weighted_Graph
import Definitions.Def_BipMatchNC_Weighted_MatchingMatrix

open Polynomial

namespace BipMatchNC.Weighted

theorem claim_3_2 {F : Type*} [Field F] (n r δ : ℕ) (G : BipGraph n) (γ : F)
    (α : Fin (n * n) → F) (hγ : OrderAtLeast γ (n * r))
    (hα : Function.Injective fun x : Fin (n * n) × Fin r => α x.1 * γ ^ (x.2 : ℕ))
    (hδ : n ≤ δ) (hr : n ^ 2 * δ < r)
    (p : Fin n × Fin (n * (r - δ)) → F)
    (hp : Matrix.vecMul p (matchingMatrix γ α r (n * (r - δ)) G) = 0) :
    LinearIndependent F fun i : {i : Fin n // ∃ k, p (i, k) ≠ 0} => blockPoly p i.1 := by sorry

end BipMatchNC.Weighted
