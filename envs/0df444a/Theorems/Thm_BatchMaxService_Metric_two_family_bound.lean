-- Prove2me | Theorems.Thm_BatchMaxService_Metric_two_family_bound
-- name    : BatchMaxService.Metric.two_family_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:31:46.652756+00:00
-- url     : https://prove2.me/theorems/9acc4a76-6ee1-4dd3-a335-a4971ce6ef14
-- title:
--   Corollary 3.4 — competitive bound from two families
-- statement:
--   Let $I$ be the full input and partition the indexed certificate groups into two colors. Each color separately has disjoint identities and ordered windows satisfying Theorem 3.3 on precisely its group subinstance. The initial dummy is optional. Different colors may share identities, and some input requests may be unused. For $\alpha\ge0$, let ALG be any extended nonnegative value satisfying the following bound; in particular, it may be the cost of the source's online execution:
--
--   $$\mathrm{ALG}\le\alpha\sum_h C_h.$$
--
--   Then
--
--   $$\mathrm{ALG}\le4\alpha\operatorname{OPT}(I).$$
--
--   This comparison combines the two certificate families while retaining the full-input elective optimum.
--
--   Differences from the source:
--   - encoding: a known nonempty finite metric and finitely many distinct request labels → sites Fin n with an arbitrary MetricSpace, an initial site, and a finite subset of natural labels; reason: every such metric and finite identity set can be enumerated, preserving all real distances, arrivals and repeated location/time pairs
--   - encoding: finite nonnegative tree minima and the elective optimum → finite tree minima and the unrestricted schedule infimum in ENNReal, with real event costs embedded by ofReal; reason: finite tree families have attained minima and finite feasible schedules have nonnegative finite cost; +infinity is the empty-infimum sentinel, never a real default zero
--   - encoding: indexed groups partitioned into two colors → one ordered group list for each Boolean color; reason: ordering each color separately preserves exactly its window hypotheses and permits cross-color identity reuse
--   - generalization: groups and ALG produced by an online execution → arbitrary admissible group families and ALG in ENNReal satisfying the certificate upper bound; reason: the comparison uses only the displayed bound and the per-color conditions, and specializes to every source execution by embedding its finite nonnegative cost
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), Corollary 3.4, (3.13)–(3.14), and Remark 3.5, printed p. 8 / PDF p. 9

import Mathlib
import Definitions.Def_BatchMaxService_Metric_Certificates

namespace BatchMaxService.Metric

/-- Corollary 3.4 and Remark 3.5, printed p. 8 / PDF 9. The two lists are the
    color classes of the original indexed groups; requests may be shared across lists. -/
theorem two_family_bound {n : ℕ} [MetricSpace (Fin n)] (I : RequestInput n)
    (families : Bool → List CertificateGroup)
    (hw : ∀ b, ValidFamily I (families b)) (ALG : ENNReal)
    (α : ℝ) (hα : 0 ≤ α)
    (hALG : ALG ≤ ENNReal.ofReal α *
      ENNReal.ofReal (certificateSum (families false) + certificateSum (families true))) :
    ALG ≤ ENNReal.ofReal (4 * α) * OPT I := by sorry

end BatchMaxService.Metric
