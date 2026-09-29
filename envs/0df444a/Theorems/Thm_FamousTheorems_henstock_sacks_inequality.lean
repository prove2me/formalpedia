-- Prove2me | Theorems.Thm_FamousTheorems_henstock_sacks_inequality
-- name    : FamousTheorems.henstock_sacks_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:55.454636+00:00
-- url     : https://prove2.me/theorems/6f2142c1-cf38-4bce-b50a-ae1d306b36d8
-- title:
--   The Henstock–Sacks inequality
-- statement:
--   **The Henstock–Sacks inequality.** Let $f$ be integrable on a box $I\subseteq\mathbb R^n$ (with respect to a gauge-type integration scheme such as the Henstock–Kurzweil, McShane or Riemann integral, and a box-additive volume), and let $\varepsilon>0$. Then there is a gauge $r$ such that:
--   1. every tagged partition of $I$ subordinate to $r$ has Riemann sum within $\varepsilon$ of $\int_I f$, and
--   2. every tagged *pre*partition $\pi$ subordinate to $r$ has Riemann sum within $\varepsilon$ of $\sum_J\int_J f$, where $J$ runs over the boxes of any prepartition covering the same region as $\pi$.
--
--   Part 2 is Henstock's lemma (also called the Saks–Henstock lemma). It is the basic tool of the theory of gauge integrals: it gives the additivity of the integral over subboxes, the monotone and dominated convergence theorems, and the fundamental theorem of calculus for the Henstock–Kurzweil integral.
--
--   **Formalization note.** Mathlib's `BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq` and `BoxIntegral.Integrable.dist_integralSum_integral_le_of_memBaseSet`, with witness gauge `h.convergenceR ε`. `l : BoxIntegral.IntegrationParams` selects the integral (Riemann, McShane, Henstock–Kurzweil and so on). The gauge depends on an extra parameter $c$ bounding the distortion of boxes, and `l.MemBaseSet I c (r c) π` says that $\pi$ is subordinate to the gauge $r\,c$ and satisfies the side conditions of `l`. The volume is a box-additive map `vol` with values in continuous linear maps $E\to F$, which covers Lebesgue measure. The target $F$ must be complete.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem henstock_sacks_inequality {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {I : BoxIntegral.Box ι} {l : BoxIntegral.IntegrationParams} {f : (ι → ℝ) → E}
    {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} (h : BoxIntegral.Integrable I l f vol) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : NNReal → (ι → ℝ) → Set.Ioi (0 : ℝ),
      (∀ (c : NNReal) (π : BoxIntegral.TaggedPrepartition I), l.MemBaseSet I c (r c) π → π.IsPartition →
        dist (BoxIntegral.integralSum f vol π) (BoxIntegral.integral I l f vol) ≤ ε) ∧
      ∀ (c : NNReal) (π : BoxIntegral.TaggedPrepartition I) (π₀ : BoxIntegral.Prepartition I),
        l.MemBaseSet I c (r c) π → π.iUnion = π₀.iUnion →
          dist (BoxIntegral.integralSum f vol π) (∑ J ∈ π₀.boxes, BoxIntegral.integral J l f vol) ≤ ε := by sorry

end FamousTheorems
