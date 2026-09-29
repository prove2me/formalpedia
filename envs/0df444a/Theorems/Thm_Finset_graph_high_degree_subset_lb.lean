-- Prove2me | Theorems.Thm_Finset_graph_high_degree_subset_lb
-- name    : Finset.graph_high_degree_subset_lb
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:11.08322+00:00
-- url     : https://prove2.me/theorems/21c8c8fe-5e34-4c25-a7f9-0df429f7f1da
-- title:
--   Dense bipartite graph has many high-degree vertices
-- statement:
--   Let $0 < \delta \le 1$ and let $A, B$ be finite sets with $A$ nonempty and $|A| = |B|$. Let $E \subseteq A \times B$ satisfy $$|E| \ge \delta\,|A|\,|B|.$$ Write $d(a) = \#\{b \in B : (a,b) \in E\}$ for the degree of $a$. Then the set of high-degree left vertices $A_{\ge} = \{a \in A : d(a) \ge \tfrac{\delta}{2}\,|B|\}$ satisfies $$|A_{\ge}| \ge \tfrac{\delta}{2}\,|A|,$$ and moreover the edges incident to $A_{\ge}$ still form a constant fraction of all pairs: $$\#\{(a,b) \in E : d(a) \ge \tfrac{\delta}{2}\,|B|\} \ge \tfrac{\delta}{2}\,|A|\,|B|.$$ This is the standard degree-regularization (Markov-type) lemma: pruning low-degree vertices from a dense bipartite graph preserves both a large vertex set and a dense edge set. In the BSG project it is used to pass to a minimum-degree subgraph before applying dependent random choice.
-- source:
--   Degree-regularization step (the set A_1) inside the proof of Fox-Sudakov, Dependent random choice, Random Structures & Algorithms 38 (2011) 68-99, Lemma 5.2 (p. 9). Not separately stated in the cited work. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L1152-L1273

import Mathlib

open scoped Pointwise

theorem Finset.graph_high_degree_subset_lb {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    (δ / 2) * (A.card : ℝ) ≤
      ((A.filter (fun a ↦
        (δ / 2) * (B.card : ℝ) ≤
          ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ))).card : ℝ) ∧
    (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤
      ((E.filter (fun p : G × G ↦
        (δ / 2) * (B.card : ℝ) ≤
          ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ))).card : ℝ) := by sorry
