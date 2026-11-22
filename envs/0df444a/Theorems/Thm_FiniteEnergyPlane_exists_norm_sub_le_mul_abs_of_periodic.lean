-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_norm_sub_le_mul_abs_of_periodic
-- name    : FiniteEnergyPlane.exists_norm_sub_le_mul_abs_of_periodic
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T15:31:48.259407+00:00
-- url     : https://prove2.me/theorems/d7c64689-aae8-4db6-a5be-b4617bde4381
-- title:
--   Continuously differentiable periodic maps are Lipschitz
-- statement:
--   Let $F$ be a real normed space and $f : \mathbb{R} \to F$ a $C^1$ map of period $1$. Then there is $L \ge 0$ with $\|f(x) - f(y)\| \le L\,|x - y|$ for all $x, y \in \mathbb{R}$.
--
--   Role: a global Lipschitz bound for smooth loops (frames, eigenvectors) parametrized by $\mathbb{R}$.
--
--   Formalization Note: the period is normalized to $1$ (`Function.Periodic f 1`).
-- source:
--   Elementary

import Mathlib

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A `C¹` map `ℝ → F` of period `1` is Lipschitz. -/
theorem exists_norm_sub_le_mul_abs_of_periodic {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ → F} (hf : ContDiff ℝ 1 f) (hper : Function.Periodic f 1) :
    ∃ L, 0 ≤ L ∧ ∀ x y, ‖f x - f y‖ ≤ L * |x - y| := by
  sorry

end FiniteEnergyPlane
