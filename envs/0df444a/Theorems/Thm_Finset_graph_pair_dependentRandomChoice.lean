-- Prove2me | Theorems.Thm_Finset_graph_pair_dependentRandomChoice
-- name    : Finset.graph_pair_dependentRandomChoice
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:12.982146+00:00
-- url     : https://prove2.me/theorems/9c6bc33c-5576-4bbd-b51c-7d307bcb406e
-- title:
--   Fox–Sudakov dependent random choice for pairs
-- statement:
--   Let $X, Y$ be nonempty finite sets and let $F \subseteq X \times Y$ have density
--   $$|F| \ge c\,|X|\,|Y| \qquad (0 < c \le 1).$$
--   Let $0 < \varepsilon \le 1$. Then there exists $U \subseteq X$ with
--   $$|U| \ge \tfrac{c}{2}\,|X|$$
--   such that few ordered pairs in $U$ have small common neighbourhood: writing $N(u) = \{y \in Y : (u,y) \in F\}$,
--   $$\#\{(u_1, u_2) \in U \times U : |N(u_1) \cap N(u_2)| < \tfrac{\varepsilon c^2}{2}\,|Y|\} \le \varepsilon\,|U|^2.$$
--   In words, a random-neighbourhood (dependent random choice) argument finds a large $U$ in which all but an $\varepsilon$-fraction of ordered pairs share a large codegree.
--
--   This is the Fox-Sudakov form of dependent random choice used in the project. In the repository it is applied once, after degree pruning, to the pruned parts: `Finset.dense_bipartite_has_path3_rectangle` first prunes $A$ to the rows $A_1$ of degree at least $\tfrac{\delta}{2}|B|$ and restricts $E$ to $E_1 = \{p \in E : p_1 \in A_1\}$, then makes a single call to this lemma on $(A_1, B, E_1)$ with $c := \tfrac{(\delta/2)|A|}{|A_1|}$ and $\varepsilon := \delta/16$. A Markov refinement on the rows of the resulting $U$ and a rare/popular split on the columns of $B$ then turn $U$ into the rectangle $A' \times B'$ in which every pair is joined by many paths of length three.
-- source:
--   Fox-Sudakov, Dependent random choice, Random Structures & Algorithms 38 (2011) 68-99, Section 5, Lemma 5.1 (p. 8). Stated here with the bad pairs counted instead of the good ones. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L898-L1149

import Mathlib

open scoped Pointwise

theorem Finset.graph_pair_dependentRandomChoice {G : Type*} [DecidableEq G]
    (X Y : Finset G) (hX : X.Nonempty) (hY : Y.Nonempty)
    (F : Finset (G × G)) (hF_sub : F ⊆ X ×ˢ Y)
    (c : ℝ) (hc_pos : 0 < c) (_hc_le : c ≤ 1)
    (hF_dense : c * (X.card : ℝ) * (Y.card : ℝ) ≤ (F.card : ℝ))
    (ε : ℝ) (hε_pos : 0 < ε) (_hε_le : ε ≤ 1) :
    ∃ U : Finset G, U ⊆ X ∧
      (c / 2) * (X.card : ℝ) ≤ (U.card : ℝ) ∧
      (((U ×ˢ U).filter fun p : G × G ↦
        (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
          (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
        (ε * c ^ 2 / 2) * (Y.card : ℝ)).card : ℝ) ≤
      ε * (U.card : ℝ) ^ 2 := by sorry
