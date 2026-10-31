-- Prove2me | Theorems.Thm_DistTransform_Distortion_mminus_case
-- name    : DistTransform.Distortion.mminus_case
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:27.370118+00:00
-- url     : https://prove2.me/theorems/6fc8a879-8b90-4971-92b4-3295e205c2aa
-- title:
--   Proof of Theorem 1, p. 8, the M− case — Eq. (4) extends to distributions bounded above but not below
-- statement:
--   Let $T$ map distributions on $\mathbb R$ to distributions on $\mathbb R$ and be lower-semicontinuous, monotone and commuting with shape transforms on $\mathcal M_0$. Let $h:(0,1)\to(0,1]$ be increasing on $(0,1)$ and satisfy eq. (4) on $\mathcal M_\infty$:
--   $$
--   (T(F))^{-1}(p)=F^{-1}(h(p)),\qquad F\in\mathcal M_\infty,\ p\in(0,1).
--   $$
--   Then the same identity holds for every $F\in\mathcal M_-$, the distributions whose support has infinite lower bound and finite upper bound:
--   $$
--   q_p^T(F)=F^{-1}(h(p)),\qquad F\in\mathcal M_-,\ p\in(0,1).
--   $$
--
--   This is the first of three cases in which the proof of Theorem 1 extends eq. (4) from $\mathcal M_\infty$ to $\mathcal M_0$.
--
--   **Formalization Note** The function $h$ and eq. (4) on $\mathcal M_\infty$ are hypotheses (they are the output of the milestone for eq. (4)). The paper's hypothesis $T:\mathcal M_0\to\mathcal M_0$ is automatic for a map from `ProbabilityMeasure ℝ` to itself and is not restated.
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), p. 8, the M− case of the proof of Theorem 1 (Eq. (5) and the display after it)

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace DistTransform.Distortion

/-- Proof of Theorem 1, p. 8, the `M−` case: for `T : M0 → M0` lower-semicontinuous, monotone
and commuting with shape transforms, eq. (4) on `M∞` extends to every `F ∈ M−`. -/
theorem mminus_case (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ)
    (hlsc : IsLSC Set.univ T) (hmono : IsMonotoneT Set.univ T)
    (hcomm : CommutesWithShape Set.univ T)
    (h : ℝ → ℝ) (hh_mono : MonotoneOn h (Set.Ioo 0 1))
    (hh_range : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < h p ∧ h p ≤ 1)
    (h4 : ∀ F ∈ Minf, ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T F) p = leftQuantile F (h p)) :
    ∀ F ∈ Mminus, ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T F) p = leftQuantile F (h p) := by sorry

end DistTransform.Distortion
