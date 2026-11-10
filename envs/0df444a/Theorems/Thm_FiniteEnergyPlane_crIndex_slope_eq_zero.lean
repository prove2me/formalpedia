-- Prove2me | Theorems.Thm_FiniteEnergyPlane_crIndex_slope_eq_zero
-- name    : FiniteEnergyPlane.crIndex_slope_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-09T22:36:51.990934+00:00
-- url     : https://prove2.me/theorems/eb19c10c-000d-4f1c-bf31-0741f373842a
-- title:
--   Index zero of the slope operator on the cylinder
-- statement:
--   Let $1 < p < \infty$, $a, b \in (0, 2\pi)$, and $\chi : \mathbb{R} \to \mathbb{R}$ smooth with $\chi'(s) = a$ for $s \le -1$ and $\chi'(s) = b$ for $s \ge 1$. Consider on the cylinder $\mathbb{R}\times S^1$ (functions on $\mathbb{R}^2$, $1$-periodic in $t$) the Cauchy-Riemann type operator
--   $$D w = \partial_s w + J_0\,\partial_t w + \chi'(s)\, w, \qquad w : \mathbb{R}\times S^1 \to \mathbb{R}^2,$$
--   i.e. `crApply` with the zero-order term $S(s,t) = \chi'(s)\,\mathbb{1}$, acting on $W^{1,p}$ (`W1p p 1`) with values in $L^p$ (`LpCyl 1 p`).
--
--   Then the index of $D : W^{1,p} \to L^p$ (`crIndex`) is $0$.
--
--   **Role.** Conjugating by the weight $e^{\chi}$ turns this operator into $\partial_s + J_0\partial_t$ on exponentially weighted spaces whose weights have slopes $a$ and $b$ at the two ends. The statement covers weights that differ at the two ends, so it applies to the tangential part of perturbation problems for holomorphic curves with a removable point at one end and a nondegenerate asymptotic end at the other.
-- source:
--   Setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry (arXiv:1011.1690), Ch. 4; used for U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- For slopes `a, b ∈ (0, 2π)` of a smooth weight `χ`, the operator `∂ₛ + J₀ ∂ₜ + χ'(s)` on the
cylinder has Fredholm index `0`. -/
theorem crIndex_slope_eq_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (a b : ℝ) (ha : a ∈ Ioo 0 (2 * π)) (hb : b ∈ Ioo 0 (2 * π))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχa : ∀ s ≤ -1, deriv χ s = a)
    (hχb : ∀ s ≥ 1, deriv χ s = b) :
    crIndex p (fun x => deriv χ x.1 • (1 : Mat 1)) = 0 := by
  sorry

end FiniteEnergyPlane
