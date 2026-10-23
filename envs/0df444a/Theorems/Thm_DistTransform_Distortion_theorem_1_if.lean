-- Prove2me | Theorems.Thm_DistTransform_Distortion_theorem_1_if
-- name    : DistTransform.Distortion.theorem_1_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:36.367397+00:00
-- url     : https://prove2.me/theorems/12147ae8-1014-4328-b30e-d0f123e05c62
-- title:
--   Proof of Theorem 1, p. 6 — a probability distortion is lower-semicontinuous, monotone and commutes with shape transforms
-- statement:
--   Let $\mathcal M=\mathcal M_0$ (all distributions on $\mathbb R$) or $\mathcal M=\mathcal M_\infty$ (distributions with bounded support), and let $T$ map $\mathcal M$ into $\mathcal M$. If $T$ is a probability distortion on $\mathcal M$, i.e. there is $g\in\mathcal H_0$ with
--   $$
--   T(F)(x)=g(F(x)),\qquad F\in\mathcal M,\ x\in\mathbb R,
--   $$
--   then $T$ is
--
--   1. lower-semicontinuous on $\mathcal M$,
--   2. monotone with respect to $\preceq_{\mathrm{st}}$ on $\mathcal M$, and
--   3. commuting with shape transforms on $\mathcal M$.
--
--   This is the "if" direction of Theorem 1 of the paper.
--
--   **Formalization Note** The hypothesis that $T$ maps $\mathcal M$ into $\mathcal M$ is the theorem's "$T:\mathcal M\to\mathcal M$". All notions are those of `DistTransform.Distortion.Model`.
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), p. 6, the "if" part of the proof of Theorem 1

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace DistTransform.Distortion

/-- Proof of Theorem 1, p. 6, the "if" part: a probability distortion `T : M → M`
(`M = M0` or `M = M∞`) is lower-semicontinuous, monotone and commutes with shape transforms. -/
theorem theorem_1_if (M : Set (ProbabilityMeasure ℝ)) (hM : M = Set.univ ∨ M = Minf)
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) (hT : Set.MapsTo T M M)
    (hT_dist : IsProbabilityDistortion M T) :
    IsLSC M T ∧ IsMonotoneT M T ∧ CommutesWithShape M T := by sorry

end DistTransform.Distortion
