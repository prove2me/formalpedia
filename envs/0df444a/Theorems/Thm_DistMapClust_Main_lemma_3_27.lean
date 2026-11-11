-- Prove2me | Theorems.Thm_DistMapClust_Main_lemma_3_27
-- name    : DistMapClust.Main.lemma_3_27
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:04:57.564208+00:00
-- url     : https://prove2.me/theorems/292d5f60-094e-49be-90ea-352b11301be2
-- title:
--   Lemma 3.27 — columns dominated by ≥ 1/ε disjoint columns cost at most a factor 1 + ε under a monotone column-symmetric norm
-- statement:
--   Let $M_1,M_2\in\mathbb R^{d\times n}_{\ge0}$ and let $f$ be a monotone, column-symmetric norm on $d\times n$ matrices. Suppose $[n]=A\sqcup B$, and write $(M)_i$ for the $i$-th column. Assume that $(M_2)_i\le(M_1)_i$ for every $i\in A$; that every $i'\in B$ has a set $N(i')\subseteq A$ with $|N(i')|\ge1/\varepsilon$ and $(M_2)_{i'}\le(M_1)_i$ for all $i\in N(i')$; and that the sets $N(i')$ are pairwise disjoint. Then
--   $$f(M_2)\le(1+\varepsilon)\,f(M_1).$$
--   The lemma charges the columns of a candidate solution that are not dominated by the optimum's to many columns that are, without zeroing any of them; it is used in the analysis of the center-finding algorithm (Lemma 3.28).
--
--   **Formalization Note.** $B$ is the complement of the `Finset` $A$; inequalities between columns are entrywise.
--
--   Differences from the source:
--   - generalization: ε is §3's fixed ε ∈ (0, 1/48) → every ε > 0; reason: the statement specializes to ε ∈ (0, 1/48); charging each B-column to ⌈1/ε⌉ permuted copies of M₁ uses no upper bound on ε
--   - encoding: partition [n] = A ⊔ B, columns (M)_i, size at least 1/ε → A : Finset (Fin n), B = Aᶜ, matrices Fin d → Fin n → ℝ with nonnegativity hypotheses, (N i').card ≥ 1/ε as reals, clause 3 as: i ∈ N i' ∩ N i'' implies i' = i''; reason: Lean convention; same statement
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), p. 42, Lemma 3.27

import Mathlib
import Definitions.Def_DistMapClust_Main_Norms

namespace DistMapClust.Main

/-- Lemma 3.27 (p. 42). Columns of `M₂` outside `A` are each dominated by at least `1/ε` columns of
`M₁` in `A`, through pairwise disjoint sets `N(i')`; columns in `A` are dominated by the same column
of `M₁`. Then `f(M₂) ≤ (1 + ε) f(M₁)` for every monotone column-symmetric norm `f`. `B` is the
complement of `A`; `ε > 0` is arbitrary (§3 fixes `ε ∈ (0, 1/48)`). -/
theorem lemma_3_27 {d n : ℕ} (ε : ℝ) (hε : 0 < ε)
    (f : Mat d n → ℝ) (hf : IsMonotoneMatrixNorm f) (hcs : IsColumnSymmetric f)
    (M₁ M₂ : Mat d n) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (A : Finset (Fin n)) (N : Fin n → Finset (Fin n))
    (h1 : ∀ i ∈ A, ∀ r, M₂ r i ≤ M₁ r i)
    (h2 : ∀ i' ∉ A, N i' ⊆ A ∧ 1 / ε ≤ ((N i').card : ℝ) ∧ ∀ i ∈ N i', ∀ r, M₂ r i' ≤ M₁ r i)
    (h3 : ∀ i ∈ A, ∀ i' ∉ A, ∀ i'' ∉ A, i ∈ N i' → i ∈ N i'' → i' = i'') :
    f M₂ ≤ (1 + ε) * f M₁ := by sorry

end DistMapClust.Main
