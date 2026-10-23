-- Prove2me | Theorems.Thm_DistTransform_Distortion_eq_4
-- name    : DistTransform.Distortion.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:32.321172+00:00
-- url     : https://prove2.me/theorems/e07c400c-bff1-41f8-ae45-133cf7d70a6d
-- title:
--   Proof of Theorem 1, Eq. (4), p. 8 — on M∞, q_p^T(F) = F^{-1}(h(p)) for an increasing h : (0, 1) → (0, 1]
-- statement:
--   Let $\mathcal M=\mathcal M_0$ or $\mathcal M=\mathcal M_\infty$, and let $T$ map $\mathcal M$ into $\mathcal M$. Suppose $T$ is lower-semicontinuous, monotone and commuting with shape transforms on $\mathcal M$. Then there is a function $h:(0,1)\to(0,1]$, increasing on $(0,1)$, such that for every distribution $F$ with bounded support
--   $$
--   q_p^T(F)=(T(F))^{-1}(p)=F^{-1}(h(p)),\qquad p\in(0,1).
--   $$
--
--   For $\mathcal M=\mathcal M_\infty$ this already shows that $T$ is a probability distortion; for $\mathcal M=\mathcal M_0$ it is the starting point of the extension to all distributions.
--
--   **Formalization Note** The conclusion is stated on $\mathcal M_\infty$ for both choices of $\mathcal M$; this is how the paper uses it ("We next focus on $\mathcal M=\mathcal M_0$. For $F\in\mathcal M_\infty$, we have shown (4)", p. 8). Since $h(p)\in(0,1]$ and $F$ has bounded support, $F^{-1}(h(p))$ is finite.
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), p. 8, Eq. (4) in the proof of Theorem 1

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace DistTransform.Distortion

/-- Proof of Theorem 1, eq. (4), p. 8: if `T : M → M` (`M = M0` or `M = M∞`) is
lower-semicontinuous, monotone and commutes with shape transforms, there is an increasing
`h : (0, 1) → (0, 1]` with `q_p^T(F) = F⁻¹(h(p))` for all `F ∈ M∞` and `p ∈ (0, 1)`. -/
theorem eq_4 (M : Set (ProbabilityMeasure ℝ)) (hM : M = Set.univ ∨ M = Minf)
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) (hT : Set.MapsTo T M M)
    (hlsc : IsLSC M T) (hmono : IsMonotoneT M T) (hcomm : CommutesWithShape M T) :
    ∃ h : ℝ → ℝ, MonotoneOn h (Set.Ioo 0 1) ∧
      (∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < h p ∧ h p ≤ 1) ∧
      ∀ F ∈ Minf, ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T F) p = leftQuantile F (h p) := by sorry

end DistTransform.Distortion
