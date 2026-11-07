-- Prove2me | Theorems.Thm_FiniteEnergyPlane_injOn_ball_of_hasStrictFDerivAt
-- name    : FiniteEnergyPlane.injOn_ball_of_hasStrictFDerivAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T15:46:16.104368+00:00
-- url     : https://prove2.me/theorems/4c646f2d-2fa7-4fc9-9f89-3d5f129566b5
-- title:
--   Local injectivity from an injective strict derivative
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F$ a real normed space. If $f : E \to F$ has a strict Fréchet derivative $f'$ at $x$ and $f'$ is injective, then $f$ is injective on a ball around $x$.
--
--   **Role.** A general statement with no assumption on the dimension of $F$, so $f'$ need not be invertible.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Mathlib

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A map with injective strict derivative at `x`, on a finite-dimensional space, is injective on a
ball around `x`. -/
theorem injOn_ball_of_hasStrictFDerivAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E →L[ℝ] F}
    {x : E} (hf : HasStrictFDerivAt f f' x) (hi : Function.Injective f') :
    ∃ δ > 0, Set.InjOn f (Metric.ball x δ) := by
  sorry

end FiniteEnergyPlane
