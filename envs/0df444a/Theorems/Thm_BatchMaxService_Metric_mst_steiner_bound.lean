-- Prove2me | Theorems.Thm_BatchMaxService_Metric_mst_steiner_bound
-- name    : BatchMaxService.Metric.mst_steiner_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:25:43.551031+00:00
-- url     : https://prove2.me/theorems/285947cb-bbcd-44b0-bcd7-fdbc4bc983c6
-- title:
--   Lemma 5.7 — terminal MST is at most twice the Steiner cost
-- statement:
--   Let $A$ be any nonempty terminal subset of a finite metric $X$. A terminal MST uses precisely $A$ as vertices, whereas a Steiner connecting tree may use any sites of $X$. Then
--
--   $$\operatorname{MST}(A)\le2\operatorname{ST}_X(A).$$
--
--   For a singleton both values are zero. There is no depot requirement, return edge or restriction on the number of terminals. This is the tree-approximation guarantee needed for the concrete general-metric algorithm.
--
--   Differences from the source:
--   - encoding: a nonempty finite terminal set and real minimum tree weights → a Finset of enumerated sites and literal finite minima in ENNReal; reason: the finite nonempty tree families attain the same minima, including zero on a singleton; no terminal or Steiner site is removed
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), Lemma 5.7, (5.18), printed p. 18 / PDF p. 19

import Mathlib
import Definitions.Def_BatchMaxService_Metric_Trees

namespace BatchMaxService.Metric

/-- Lemma 5.7, printed p. 18 / PDF 19. Steiner vertices range over the whole
    metric, whereas the terminal MST has exactly A as its vertices. -/
theorem mst_steiner_bound {n : ℕ} [MetricSpace (Fin n)]
    (A : Finset (Fin n)) (hA : A.Nonempty) :
    MSTCost A ≤ 2 * SteinerCost A := by sorry

end BatchMaxService.Metric
