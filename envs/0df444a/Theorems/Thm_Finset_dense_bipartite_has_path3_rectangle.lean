-- Prove2me | Theorems.Thm_Finset_dense_bipartite_has_path3_rectangle
-- name    : Finset.dense_bipartite_has_path3_rectangle
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:10.008945+00:00
-- url     : https://prove2.me/theorems/59b0990a-45ac-4a27-80a5-3c4a3ca312bc
-- title:
--   Dense bipartite graph contains a $3$-path-rich rectangle
-- statement:
--   Let $G$ be an additive commutative group, let $0 < \delta \le 1$, and let $A, B \subseteq G$ be finite sets with $A$ nonempty and $|A| = |B|$. Let $E \subseteq A \times B$ be a set of edges with
--   $$|E| \ge \delta\,|A|\,|B|.$$
--   Then there exist $A' \subseteq A$ and $B' \subseteq B$ with
--   $$|A'| \ge \tfrac{\delta}{8}\,|A|, \qquad |B'| \ge \tfrac{\delta}{8}\,|A|,$$
--   such that for every $a \in A'$ and every $b \in B'$,
--   $$\#\{(b_1, a_2) \in B \times A : (a,b_1) \in E,\ (a_2,b_1) \in E,\ (a_2,b) \in E\} \ \ge\ \tfrac{\delta^5}{2^{12}}\,|A|^2.$$
--
--   This is the rectangle lemma that the Balog-Szemeredi-Gowers argument in this project consumes, proved along the Fox-Sudakov dependent-random-choice route: degree pruning, one application of pair dependent random choice, a Markov refinement on rows, and a rare/popular split on columns. It is not a transcription of Fox-Sudakov, *Dependent random choice*, Lemma 5.2; it departs from that lemma in two ways, recorded here.
--
--   **Deviation 1: the counted set carries no distinctness conditions.** Fox-Sudakov count genuine paths of length three. Their proof produces at least $c^2n/32 - 1$ neighbours $a_2 \ne a$ of $b$ in the core set, and for each of those at least $c^3n/32 - 1$ common neighbours $b_1 \ne b$; the two "$-1$" terms are exactly those distinctness corrections, and the product of the two factors is what is bounded below by $2^{-12}c^5n^2$. The set counted in the statement above is the plain filter of $B \times A$ by the three edge conditions, with no requirement $a_2 \ne a$ or $b_1 \ne b$, so degenerate pairs are admitted. The count above therefore ranges over a strictly larger set and the conclusion is weaker than Lemma 5.2's: Lemma 5.2's bound implies the bound above, while the bound above does not give Lemma 5.2's. The weaker form is sound for the Balog-Szemeredi-Gowers use, because the representation consumed downstream,
--   $$y \;=\; a + b \;=\; (a + b_1) - (a_2 + b_1) + (a_2 + b) \;=\; x - x' + x'',$$
--   is valid for degenerate paths too: it needs only that the three pairs are edges, never that the vertices are distinct.
--
--   **Deviation 2: a guaranteed lower bound replaces the exact density.** After pruning to the rows $A_1 = \{a \in A : \#\{b \in B : (a,b) \in E\} \ge \tfrac{\delta}{2}|B|\}$, Fox-Sudakov run dependent random choice with the exact edge density $c_1 = e(A_1, B)/(|A_1|\,|B|)$. The proof formalized here instead sets
--   $$c_0 \;=\; \frac{(\delta/2)\,|A|}{|A_1|}$$
--   and runs dependent random choice with $c_0$. Since $e(A_1,B) \ge \tfrac{\delta}{2}|A|\,|B|$, one has $c_0 \le c_1$ — this is the lower bound Fox-Sudakov themselves display — so the density hypothesis of the dependent-random-choice lemma is met and the argument is sound, but every bound downstream is stated in terms of $c_0$ rather than $c_1$.
--
--   A third, smaller difference: the column bound is stated here as $|B'| \ge \tfrac{\delta}{8}|A|$, where Fox-Sudakov state $|B'| \ge \tfrac{c}{4}n$; only the weaker $\delta/8$ form is claimed.
--
--   The conclusion feeds the Tao-Vu triple-count injection, which converts path richness plus a small restricted sumset into a bound on the honest sumset $|A' + B'|$.
-- source:
--   Fox-Sudakov, Dependent random choice, Random Structures & Algorithms 38 (2011) 68-99, Section 5.1, Lemma 5.2 (p. 9). Formalized with the source's a' != a and b' != b distinctness terms dropped, so the path count admits degenerate paths and the conclusion is weaker than the paper's; sound for the BSG application. Compare Tao-Vu, Additive Combinatorics, Cambridge Univ. Press (2006), Corollary 6.20, which is a different variant with different constants. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L1932-L1970

import Mathlib

open scoped Pointwise

theorem Finset.dense_bipartite_has_path3_rectangle {G : Type*} [AddCommGroup G] [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        (δ^5 / 2^12) * (A.card : ℝ)^2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by sorry
