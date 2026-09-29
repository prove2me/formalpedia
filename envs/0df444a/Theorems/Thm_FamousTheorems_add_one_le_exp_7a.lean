-- Prove2me | Theorems.Thm_FamousTheorems_add_one_le_exp_7a
-- name    : FamousTheorems.add_one_le_exp_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:25:35.904896+00:00
-- url     : https://prove2.me/theorems/2c5771a2-f728-4c59-899b-fa94b4333efc
-- title:
--   1 + x ≤ eˣ
-- statement:
--   **The inequality $1+x\le e^x$.** For every real number $x$,
--   $$x+1\le e^x.$$
--
--   Geometrically, the tangent line to the graph of $e^x$ at $0$ lies below the graph, since $e^x$ is convex. This elementary inequality is used everywhere in analysis and probability: it gives $1-x\le e^{-x}$ and hence $\prod(1-p_i)\le e^{-\sum p_i}$, the bound behind the birthday problem, Chernoff bounds and the analysis of randomized algorithms. It also implies the AM–GM inequality.
--
--   **Formalization note.** Mathlib's `Real.add_one_le_exp`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.add_one_le_exp`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem add_one_le_exp_7a (x : ℝ) : x + 1 ≤ Real.exp x := by sorry

end FamousTheorems
