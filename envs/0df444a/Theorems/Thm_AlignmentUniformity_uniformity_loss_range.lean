-- Prove2me | Theorems.Thm_AlignmentUniformity_uniformity_loss_range
-- name    : AlignmentUniformity.uniformity_loss_range
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:30:44.879976+00:00
-- url     : https://prove2.me/theorems/2952fc42-e9b5-4b9d-a0d2-186ce9b0c9a7
-- title:
--   Corollary 1: range of $\mathcal{L}_\mathsf{uniform}$
-- statement:
--   Let $m\ge1$, $t>0$, let $p_{\mathrm{data}}$ be a probability distribution on $\mathbb{R}^n$, and let $f:\mathbb{R}^n\to S^{m-1}$ be a measurable encoder. Then
--
--   $$-2t+\log{}_0F_1(;\tfrac m2;t^2)\ \le\ \mathcal{L}_{\mathsf{uniform}}(f;t)\ \le\ 0.$$
--
--   1. The lower bound is attained exactly when $f$ is perfectly uniform.
--   2. The upper bound $0$ is attained exactly when $f$ is degenerate, that is, $f(x)=u$ for $p_{\mathrm{data}}$-almost every $x$, for some fixed $u$.
--   3. As a function of $m\ge1$, the lower bound strictly decreases, and $\lim_{m\to\infty}\big(-2t+\log{}_0F_1(;\frac m2;t^2)\big)=-2t$ (eq. 7).
--
--   **Formalization Note** The paper says the bounds are "achieved only by" perfectly uniform and degenerate encoders. Both directions are stated, since each converse follows directly from Proposition 3 and the definitions.
-- source:
--   Wang and Isola, Understanding Contrastive Representation Learning through Alignment and Uniformity on the Hypersphere, ICML 2020, arXiv:2005.10242v10, Appendix A.1.1, Corollary 1, eq. (7), p. 17

import Mathlib
import Definitions.Def_AlignmentUniformity_Basic

open MeasureTheory Filter Topology

namespace AlignmentUniformity

theorem uniformity_loss_range {n m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t)
    (pdata : Measure (Vec n)) [IsProbabilityMeasure pdata]
    (f : Vec n → Vec m) (hf : IsEncoder f) :
    -2 * t + Real.log (hyp0F1 ((m : ℝ) / 2) (t ^ 2)) ≤ uniformLoss pdata f t ∧
      uniformLoss pdata f t ≤ 0 ∧
      (uniformLoss pdata f t = -2 * t + Real.log (hyp0F1 ((m : ℝ) / 2) (t ^ 2)) ↔
        PerfectlyUniform pdata f) ∧
      (uniformLoss pdata f t = 0 ↔ ∃ u : Vec m, ∀ᵐ x ∂pdata, f x = u) ∧
      StrictAntiOn (fun m' : ℕ => -2 * t + Real.log (hyp0F1 ((m' : ℝ) / 2) (t ^ 2)))
        (Set.Ici 1) ∧
      Tendsto (fun m' : ℕ => -2 * t + Real.log (hyp0F1 ((m' : ℝ) / 2) (t ^ 2))) atTop
        (𝓝 (-2 * t)) := by sorry

end AlignmentUniformity
