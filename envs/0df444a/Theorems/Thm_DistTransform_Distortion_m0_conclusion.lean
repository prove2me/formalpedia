-- Prove2me | Theorems.Thm_DistTransform_Distortion_m0_conclusion
-- name    : DistTransform.Distortion.m0_conclusion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:26.710354+00:00
-- url     : https://prove2.me/theorems/9118340a-aaf4-44e8-84f0-771125516099
-- title:
--   Proof of Theorem 1, p. 10 — on M0, q_p^T(F) = F^{-1}(h(p)) for an increasing h : (0, 1) → (0, 1)
-- statement:
--   Let $T$ map distributions on $\mathbb R$ to distributions on $\mathbb R$ and be lower-semicontinuous, monotone and commuting with shape transforms on $\mathcal M_0$. Then there is a function $h:(0,1)\to(0,1)$, increasing on $(0,1)$, such that for every distribution $F$ on $\mathbb R$
--   $$
--   q_p^T(F)=(T(F))^{-1}(p)=F^{-1}(h(p)),\qquad p\in(0,1).
--   $$
--
--   Together with the remark on p. 4 this proves the "only if" direction of Theorem 1 for $\mathcal M=\mathcal M_0$.
--
--   **Formalization Note** Both bounds $0<h(p)<1$ are part of the conclusion; they make $F^{-1}(h(p))$ finite for every distribution.
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), p. 10, the conclusion of the case M = M0 in the proof of Theorem 1

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace DistTransform.Distortion

/-- Proof of Theorem 1, p. 10, the case `M = M0`: for `T : M0 → M0` lower-semicontinuous,
monotone and commuting with shape transforms there is an increasing `h : (0, 1) → (0, 1)` with
`q_p^T(F) = F⁻¹(h(p))` for all `F ∈ M0` and `p ∈ (0, 1)`. -/
theorem m0_conclusion (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ)
    (hlsc : IsLSC Set.univ T) (hmono : IsMonotoneT Set.univ T)
    (hcomm : CommutesWithShape Set.univ T) :
    ∃ h : ℝ → ℝ, MonotoneOn h (Set.Ioo 0 1) ∧
      (∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < h p ∧ h p < 1) ∧
      ∀ (F : ProbabilityMeasure ℝ), ∀ p ∈ Set.Ioo (0 : ℝ) 1,
        leftQuantile (T F) p = leftQuantile F (h p) := by sorry

end DistTransform.Distortion
