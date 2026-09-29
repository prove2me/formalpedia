-- Prove2me | Theorems.Thm_CrossingLemma
-- name    : CrossingLemma
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T19:52:02.493107+00:00
-- url     : https://prove2.me/theorems/68421f78-7ddc-48d0-960e-4267ea8899e7
-- title:
--   The crossing lemma for finite simple graphs
-- statement:
--   Let $G$ be a finite simple graph with $n$ vertices and $m$ edges. If $n\ge 1$ and $m\ge 4n$, then its crossing number satisfies
--
--   $$
--   \frac{m^3}{100n^2}\le \operatorname{cr}(G).
--   $$
--
--   Here $\operatorname{cr}(G)$ denotes the minimum number of crossings among ordinary polygonal drawings of $G$. This is the quantitative crossing lemma used to turn a sufficiently dense graph into a lower bound for its crossing number, and is the principal combinatorial-geometric estimate in the unit-distance application.
--
--   **Formalization Note** The Lean statement expresses $n$ and $m$ as `Fintype.card V` and `G.edgeFinset.card`, respectively, and casts the resulting natural-number quantities to $\mathbb{R}$.
-- source:
--   wpegden/crossing-consequences@8769d142033fce042f502bf2857afb6b1375b5c3, Tablet/CrossingLemma.lean, declaration `CrossingLemma`, lines 14–19: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/CrossingLemma.lean#L14-L19

import Definitions.Def_CrossingNumber

open Classical
open scoped Real
noncomputable section

theorem CrossingLemma {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet]
    (hn : 1 ≤ Fintype.card V)
    (he : 4 * Fintype.card V ≤ G.edgeFinset.card) :
    (G.edgeFinset.card : ℝ) ^ 3 / (100 * (Fintype.card V : ℝ) ^ 2) ≤
      (CrossingNumber G : ℝ) := by sorry
