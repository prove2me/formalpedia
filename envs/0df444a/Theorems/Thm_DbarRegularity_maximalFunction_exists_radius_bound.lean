-- Prove2me | Theorems.Thm_DbarRegularity_maximalFunction_exists_radius_bound
-- name    : DbarRegularity.maximalFunction_exists_radius_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T23:20:30.915293+00:00
-- url     : https://prove2.me/theorems/459eae10-4d16-487a-aec2-c3e310a45d6d
-- title:
--   Uniformly bounded radii for the superlevel sets of the maximal function of an integrable f
-- statement:
--   Let $Mf$ be the Hardy–Littlewood maximal function of $f:\mathbb{R}^d\to\mathbb{C}$,
--   $$Mf(x)=\sup_{r>0}\frac{1}{|B(x,r)|}\int_{B(x,r)}|f(y)|\,dy\in[0,\infty],$$
--   where $B(x,r)$ is the open ball and $|\cdot|$ is Lebesgue measure. Suppose $\int_{\mathbb{R}^d}|f|<\infty$ and $\alpha>0$. Then there is $R<\infty$ such that for every $x$ with $Mf(x)>\alpha$ there is a radius $0<\rho\le R$ with
--   $$\alpha\,|B(x,\rho)|<\int_{B(x,\rho)}|f(y)|\,dy .$$
--
--   So the balls on which the average of $|f|$ exceeds $\alpha$ can be taken with radii bounded uniformly over the whole superlevel set $\{Mf>\alpha\}$.
--
--   **Formalization Note.** `maximalFunction f` (from `Definitions.Def_DbarRegularity_Setting`) is `ℝ≥0∞`-valued; $\alpha$ is in `ℝ≥0` and $R,\rho$ are real. The hypothesis $\int|f|<\infty$ is `∫⁻ y, ‖f y‖ₑ ≠ ⊤`; no measurability is assumed. The case $d=0$ is included.
-- source:
--   Auxiliary statement for E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 1.3, Theorem 1 (b), p. 5

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

open MeasureTheory Metric
open scoped ENNReal NNReal

/-- If `∫ |f| < ∞` and `α > 0`, there is `R` such that at every point where `M f > α` some ball of
radius at most `R` centred there has `α |B| < ∫_B |f|`. -/
theorem maximalFunction_exists_radius_bound (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (α : ℝ≥0) (hα : 0 < α)
    (hS : ∫⁻ y, ‖f y‖ₑ ≠ ⊤) :
    ∃ R : ℝ, ∀ x, (α : ℝ≥0∞) < maximalFunction f x → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      (α : ℝ≥0∞) * volume (ball x ρ) < ∫⁻ y in ball x ρ, ‖f y‖ₑ := by sorry

end DbarRegularity
