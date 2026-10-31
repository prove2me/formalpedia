-- Prove2me | Theorems.Thm_DistTransform_Distortion_mplus_case
-- name    : DistTransform.Distortion.mplus_case
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:35.316046+00:00
-- url     : https://prove2.me/theorems/28210ff6-206c-49ad-b2d9-19ed12335ff7
-- title:
--   Proof of Theorem 1, p. 9, the M+ case — h(p) < 1, and Eq. (4) extends to distributions bounded below but not above
-- statement:
--   Let $T$ map distributions on $\mathbb R$ to distributions on $\mathbb R$ and be lower-semicontinuous, monotone and commuting with shape transforms on $\mathcal M_0$. Let $h:(0,1)\to(0,1]$ be increasing on $(0,1)$ and satisfy eq. (4) on $\mathcal M_\infty$:
--   $$
--   (T(F))^{-1}(p)=F^{-1}(h(p)),\qquad F\in\mathcal M_\infty,\ p\in(0,1).
--   $$
--   Then
--
--   1. $h(p)<1$ for every $p\in(0,1)$, and
--   2. for every $F\in\mathcal M_+$, the distributions whose support has finite lower bound and infinite upper bound,
--   $$
--   q_p^T(F)=F^{-1}(h(p)),\qquad p\in(0,1).
--   $$
--
--   This is the second of three cases in which the proof of Theorem 1 extends eq. (4) from $\mathcal M_\infty$ to $\mathcal M_0$; it is also where the level function is shown to avoid the value $1$.
--
--   **Formalization Note** The function $h$ and eq. (4) on $\mathcal M_\infty$ are hypotheses. The conclusion $h(p)<1$ is part of the statement: without it, $F^{-1}(h(p))$ would be infinite for $F\in\mathcal M_+$ and the real-valued quantile would return a meaningless value.
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), p. 9, the M+ case of the proof of Theorem 1 (Eq. (6) and the displays after it)

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace DistTransform.Distortion

/-- Proof of Theorem 1, p. 9, the `M+` case: for `T : M0 → M0` lower-semicontinuous, monotone
and commuting with shape transforms, the level function of eq. (4) satisfies `h(p) < 1` and
eq. (4) extends to every `F ∈ M+`. -/
theorem mplus_case (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ)
    (hlsc : IsLSC Set.univ T) (hmono : IsMonotoneT Set.univ T)
    (hcomm : CommutesWithShape Set.univ T)
    (h : ℝ → ℝ) (hh_mono : MonotoneOn h (Set.Ioo 0 1))
    (hh_range : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < h p ∧ h p ≤ 1)
    (h4 : ∀ F ∈ Minf, ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T F) p = leftQuantile F (h p)) :
    (∀ p ∈ Set.Ioo (0 : ℝ) 1, h p < 1) ∧
      ∀ F ∈ Mplus, ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T F) p = leftQuantile F (h p) := by sorry

end DistTransform.Distortion
