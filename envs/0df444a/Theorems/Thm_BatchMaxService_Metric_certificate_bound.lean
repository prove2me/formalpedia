-- Prove2me | Theorems.Thm_BatchMaxService_Metric_certificate_bound
-- name    : BatchMaxService.Metric.certificate_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:32:55.870876+00:00
-- url     : https://prove2.me/theorems/2452d0c9-101c-4f46-b417-87a4781161b6
-- title:
--   Theorem 3.3 — certificate bound for request groups
-- statement:
--   Let $I$ be a finite elective-service input, partitioned into nonempty groups $G_1,\ldots,G_m$, optionally augmented by the free dummy at $(s_0,0)$. Let $0=T_0<T_1<\cdots<T_m$, with the first window closed on the left and all later windows open on the left. Every member of $G_k$ arrives in its window. Suppose
--
--   $$0\le C_k\le T_k-T_{k-1},\qquad C_k\le\operatorname{ST}_X(\{x(q):q\in G_k\}).$$
--
--   Every feasible elective schedule $\sigma$ then satisfies
--
--   $$\sum_k C_k\le\operatorname{Delay}(\sigma)+2\operatorname{Mov}(\sigma)\le2\operatorname{cost}(\sigma),\qquad\sum_k C_k\le2\operatorname{OPT}(I).$$
--
--   The offline schedule need not use these groups as batches. This provides the lower bound on unrestricted offline cost used by the online comparisons.
--
--   Differences from the source:
--   - encoding: a known nonempty finite metric and finitely many distinct request labels → sites Fin n with an arbitrary MetricSpace, an initial site, and a finite subset of natural labels; reason: every such metric and finite identity set can be enumerated, preserving all real distances, arrivals and repeated location/time pairs
--   - encoding: finite nonnegative tree minima and the elective optimum → finite tree minima and the unrestricted schedule infimum in ENNReal, with real event costs embedded by ofReal; reason: finite tree families have attained minima and finite feasible schedules have nonnegative finite cost; +infinity is the empty-infimum sentinel, never a real default zero
--   - encoding: one optional free dummy at the initial site and time zero → the distinct Option label none, with actual requests some q; reason: no actual identity is reused or served twice, and the window conditions allow the dummy only in the first group
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), Theorem 3.3, (3.4)–(3.5), printed pp. 7–8 / PDF pp. 8–9

import Mathlib
import Definitions.Def_BatchMaxService_Metric_Certificates

namespace BatchMaxService.Metric

/-- Theorem 3.3, printed pp. 7–8 / PDF 8–9, including both schedule inequalities
    and the infimum consequence. The optional dummy is not a second real service. -/
theorem certificate_bound {n : ℕ} [MetricSpace (Fin n)] (I : RequestInput n)
    (gs : List CertificateGroup) (hw : ValidFamily I gs)
    (hcover : realGroupIds gs = I.ids) :
    (∀ σ : Schedule n, Feasible I σ →
      certificateSum gs ≤ delay I σ + 2 * movement σ ∧
      delay I σ + 2 * movement σ ≤ 2 * cost I σ) ∧
    ENNReal.ofReal (certificateSum gs) ≤ 2 * OPT I := by sorry

end BatchMaxService.Metric
