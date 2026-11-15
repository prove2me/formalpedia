-- Prove2me | Theorems.Thm_FengLiYangMatching_General_Supplement_lemma_B_1
-- name    : FengLiYangMatching.General.Supplement.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:21:29.783193+00:00
-- url     : https://prove2.me/theorems/0b56de71-64a4-4ac8-9fe4-a0ef879db32a
-- title:
--   Lemma B.1 — Single-endpoint comparison with weights 7 and 4
-- statement:
--   Let $B$ be the background graph in the local setup, let $x_i$ be a selected endpoint and $y_i$ one of its reference vertices, and delete any other vertex $z$. Add the independently retained edges of $x_i$ to the remaining graph. Write $n_i,r_i$ for the indicators that $x_i,y_i$ are matched by Greedy there, and $\mu_i$ for the probability that the baseline Greedy run on $B$ matches $y_i$. For $7/11\le q\le1$,
--
--   $$\mathbb E[7n_i+4r_i]\ge7-3\mu_i.$$
--
--   The same inequality holds for every fixed choice of retention outcomes on the other edges incident to $x_i$. The expectation still averages the common uniform order and the distinguished reference-edge coin. The local configuration and experiments are the published Local definitions. This is the single-endpoint supporting result for the triangle-free comparison.
--
--   Differences from the source:
--   - encoding: arbitrary finite labelled vertex set → Fin n and unordered Sym2 edges, for every natural n; reason: every finite simple graph has such a labelling; the representation removes no instance
--   - encoding: also after fixing other retention outcomes → singleMean with an arbitrary fixed subset excluding the distinguished reference edge; reason: only that reference coin and the common uniform edge order are averaged; unused outcomes have no effect
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018 (October 2026), Lemma B.1, p. 26.

import Definitions.Def_FengLiYangMatching_General_Local

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace FengLiYangMatching.General.Supplement

theorem lemma_B_1 {n : ℕ} (d : Local n) (hd : d.Valid)
    (q : ℝ) (hq : 7/11 ≤ q) (hq1 : q ≤ 1)
    (x y z : Fin n) (hx : x ∈ ({d.x1,d.x2} : Finset (Fin n)))
    (hy : y ∈ d.marked) (hz1 : z ≠ d.x1) (hz2 : z ≠ d.x2) (hzy : z ≠ y)
    (hedge : s(x,y) ∈ d.potential) (fixed : EdgeSet n)
    (hfixed : fixed ⊆ d.potential) (href : s(x,y) ∉ fixed) :
    singleMean d q s(x,y) fixed (fun σ r =>
      7 * count {x} (deletedRun d x z σ r) + 4 * count {y} (deletedRun d x z σ r))
      ≥ 7 - 3 * mu d y := by sorry

end FengLiYangMatching.General.Supplement
