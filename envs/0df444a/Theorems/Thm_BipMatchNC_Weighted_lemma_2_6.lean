-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_lemma_2_6
-- name    : BipMatchNC.Weighted.lemma_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:12:01.823019+00:00
-- url     : https://prove2.me/theorems/e27d6cc2-8b89-4cb9-98ec-e320063c76be
-- title:
--   Lemma 2.6: an s-dimensional space of polynomials of degree ≤ D has at most sD/(r − s + 1) r-folded roots in T, and Σ_{α∈T} Z_r(P, α) ≤ sD/(r − s + 1)
-- statement:
--   Let $F$ be a field, $T\subseteq F$ finite, $\gamma\in F$ and $r,D,s\in\mathbb N$ such that the set $S=\{\alpha\gamma^\ell:\alpha\in T,\ 0\le\ell\le r-1\}$ has $|T|\,r$ distinct elements and $\gamma$ has order more than $D$. Let $P\subseteq F[x]$ be a linear space of polynomials of degree at most $D$ of dimension $s$, with $r\ge s$. Then
--
--   1. the number of $r$-folded roots of $P$ in $T$ (elements $\alpha\in T$ that are $r$-folded roots of some nonzero $p\in P$) is at most $\frac{sD}{r-s+1}$, and
--   2. more generally
--   $$\sum_{\alpha\in T}Z_r(P,\alpha)\le\frac{sD}{r-s+1},$$
--   where $Z_r(P,\alpha)$ is the dimension of the subspace of $P$ of polynomials vanishing at $\alpha,\alpha\gamma,\dots,\alpha\gamma^{r-1}$.
--
--   This is the subspace-design property of Guruswami and Kopparty; Claim 3.2 and Theorem 3.1 use part 1 to count the folded roots of the block polynomials of a left kernel vector of $M(G)$.
--
--   Differences from the source:
--   - reading: Definition 2.5: α is an r-folded root of P if it is an r-folded root of some polynomial p(x) ∈ P → … of some nonzero p ∈ P (IsFoldedRootOfSpace); reason: obvious typo (finding I1): the proof says 'some nonzero p0(x) ∈ P'; literally the zero polynomial makes part 1 false
--   - encoding: T ⊆ F with S = { αγ^ℓ | α ∈ T, 0 ≤ ℓ ≤ r − 1 } of |T|r distinct elements → T : Finset F and Set.ncard {x | ∃ α ∈ T, ∃ ℓ < r, x = α * γ ^ ℓ} = T.card * r; reason: |T|r is a number, so T is finite; same condition
--   - encoding: γ has order more than D → OrderAtLeast γ (D + 1); reason: multiplicative order, as in Lemma 2.4
--   - encoding: P ⊆ F[x]≤D a linear space of dimension s → P : Submodule F F[X], P ≤ degreeLE F D, Module.finrank F P = s; reason: same object; P is finite-dimensional because it lies in F[x]≤D
--   - encoding: Z_r(P, α): the number of linearly independent polynomials in P for which α is an r-folded root → Module.finrank F (P ⊓ foldedRootSpace γ r α); reason: the polynomials of P with α as an r-folded root form a subspace, and its dimension is the largest size of a linearly independent family in it
--   - encoding: the bounds sD/(r − s + 1) → the counts cast to ℚ and compared with (s · D) / (r − s + 1) in ℚ; reason: same rational number; r − s + 1 ≥ 1
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 7 (PDF 8), Lemma 2.6

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Folded

open Polynomial

namespace BipMatchNC.Weighted

theorem lemma_2_6 {F : Type*} [Field F] (T : Finset F) (γ : F) (r D s : ℕ)
    (hT : {x : F | ∃ α ∈ T, ∃ ℓ : ℕ, ℓ < r ∧ x = α * γ ^ ℓ}.ncard = T.card * r)
    (hγ : OrderAtLeast γ (D + 1))
    (P : Submodule F F[X]) (hP : P ≤ Polynomial.degreeLE F (D : WithBot ℕ))
    (hs : Module.finrank F P = s) (hrs : s ≤ r) :
    (({α : F | α ∈ T ∧ IsFoldedRootOfSpace γ r P α}.ncard : ℕ) : ℚ) ≤
        ((s : ℚ) * D) / ((r : ℚ) - s + 1) ∧
      (((∑ α ∈ T, foldedRootMult γ r P α : ℕ)) : ℚ) ≤ ((s : ℚ) * D) / ((r : ℚ) - s + 1) := by sorry

end BipMatchNC.Weighted
