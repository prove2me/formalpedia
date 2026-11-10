-- Prove2me | Theorems.Thm_CauchyRiemannIndex_enorm_le_w1pNorm_of_isTestSection
-- name    : CauchyRiemannIndex.enorm_le_w1pNorm_of_isTestSection
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-09T16:38:21.495201+00:00
-- url     : https://prove2.me/theorems/e14f1812-9ef6-4fae-b6dc-eeaa6d2c525b
-- title:
--   Pointwise bound of test sections on the cylinder by the W^{1,p} norm, p > 2
-- statement:
--   Let $2 < p < \infty$. There is a constant $C$ such that for every test section $u : \mathbb{R}\times\mathbb{R} \to \mathbb{R}^{2n}$ (smooth, $1$-periodic in $t$, vanishing for large $|s|$) and every point $x$,
--   $$|u(x)| \le C\,\big(\|u\|_{L^p} + \|\partial_s u\|_{L^p} + \|\partial_t u\|_{L^p}\big),$$
--   the $L^p$ norms taken on the strip $\mathbb{R}\times[0,1)$ (`w1pNorm p u`).
--
--   **Role.** The sup-norm bound on the dense class of $W^{1,p}(\mathbb{R}\times S^1)$; it extends to all of $W^{1,p}$.
-- source:
--   Standard Sobolev embedding on the cylinder; setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry (arXiv:1011.1690), Ch. 4

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal NNReal

/-- Pointwise bound on the cylinder `ℝ × S¹` for `2 < p < ∞`: there is a constant `C` with
`‖u x‖ ≤ C ‖u‖_{W^{1,p}}` for every test section `u` and every point `x`. -/
theorem enorm_le_w1pNorm_of_isTestSection {n : ℕ} (p : ℝ≥0∞) (hp : 2 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ, ∀ u : ℝ × ℝ → Vec n, IsTestSection u → ∀ x : ℝ × ℝ,
      ‖u x‖ₑ ≤ ENNReal.ofReal C * w1pNorm p u := by
  sorry

end CauchyRiemannIndex
