-- Prove2me | Theorems.Thm_DistTransform_Distortion_theorem_1
-- name    : DistTransform.Distortion.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:27.832661+00:00
-- url     : https://prove2.me/theorems/26783b41-b99f-4ec5-9503-3f696fb1361b
-- title:
--   Theorem 1, p. 6 — on M0 or M∞, T is lower-semicontinuous, monotone and commuting with shape transforms iff it is a probability distortion
-- statement:
--   Let $\mathcal M=\mathcal M_0$ (all distributions on $\mathbb R$) or $\mathcal M=\mathcal M_\infty$ (distributions with bounded support), and let $T:\mathcal M\to\mathcal M$ be a distributional transform. Then $T$ is lower-semicontinuous, monotone and commuting with shape transforms on $\mathcal M$ if and only if $T$ is a probability distortion on $\mathcal M$, i.e. there is $g\in\mathcal H_0$ with
--   $$
--   T(F)(x)=g(F(x)),\qquad F\in\mathcal M,\ x\in\mathbb R.
--   $$
--
--   Probability distortions are the basic objects of rank-dependent utility and dual utility theory, of distortion risk measures and of cumulative prospect theory. The theorem characterizes them among all transforms of distributions by three order-theoretic properties, with no linearity or continuity assumption on $g$ beyond those forced by the properties themselves.
--
--   **Formalization Note** Distributions are `ProbabilityMeasure ℝ`; $\mathcal M_0$ is `Set.univ` and $\mathcal M_\infty$ is `Minf`. The hypothesis that $T$ maps $\mathcal M$ into $\mathcal M$ is the theorem's "$T:\mathcal M\to\mathcal M$". Being a probability distortion is the cdf identity above, for some $g$ that is increasing and right-continuous on $[0,1]$ with $g(0)=0$, $g(1)=1$. Lower-semicontinuity is the paper's closure property of Definition 2, not Mathlib's `LowerSemicontinuous`, and weak convergence is convergence in Mathlib's topology on `ProbabilityMeasure ℝ`.
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), p. 6, Theorem 1

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace DistTransform.Distortion

/-- Theorem 1, p. 6. Let `T : M → M` with `M = M0` or `M = M∞`. Then `T` is
lower-semicontinuous, monotone and commuting with shape transforms if and only if it is a
probability distortion. -/
theorem theorem_1 (M : Set (ProbabilityMeasure ℝ)) (hM : M = Set.univ ∨ M = Minf)
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) (hT : Set.MapsTo T M M) :
    (IsLSC M T ∧ IsMonotoneT M T ∧ CommutesWithShape M T) ↔ IsProbabilityDistortion M T := by sorry

end DistTransform.Distortion
