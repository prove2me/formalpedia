-- Prove2me | Theorems.Thm_DbarRegularity_eLpNorm_le_eLpNorm_deriv_of_tsupport_subset_ball
-- name    : DbarRegularity.eLpNorm_le_eLpNorm_deriv_of_tsupport_subset_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T23:36:05.444824+00:00
-- url     : https://prove2.me/theorems/985c8d70-141d-46a3-9987-55bdf9136b50
-- title:
--   A one-dimensional L^p Poincaré inequality with constant 2R
-- statement:
--   Let $E$ be a real Banach space, $R\in\mathbb{R}$, $p\in[1,\infty)$ real, and let $g:\mathbb{R}\to E$ be continuously differentiable with $\operatorname{supp} g\subseteq(-R,R)$ (closed support). Then
--   $$\|g\|_{L^p(\mathbb{R})}\le 2R\,\|g'\|_{L^p(\mathbb{R})} .$$
--   This is a one-dimensional $L^p$ Poincaré inequality for functions vanishing outside a bounded interval, with an explicit constant independent of $p$.
--
--   **Formalization Note** `ContDiff ℝ 1 g` is $C^1$ smoothness, `deriv g` is $g'$, and "support in $(-R,R)$" is `tsupport g ⊆ ball 0 R` (for $R\le 0$ this forces $g=0$). The norms are `eLpNorm _ (ENNReal.ofReal p) volume` with respect to Lebesgue measure, valued in $[0,\infty]$, and $2R$ enters as `ENNReal.ofReal (2 * R)`.
-- source:
--   C. Abbas, H. Hofer, Holomorphic Curves and Global Questions in Contact Geometry, Birkhäuser Advanced Texts Basler Lehrbücher, Birkhäuser (2019), https://doi.org/10.1007/978-3-030-11803-7, § 4.2, p. 102

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal

/-- One-dimensional `L^p` Poincaré inequality: for real `p ≥ 1`, a `C¹` map `g : ℝ → E` with support
in `(-R, R)` satisfies `‖g‖_{L^p} ≤ 2R ‖g'‖_{L^p}`. -/
theorem eLpNorm_le_eLpNorm_deriv_of_tsupport_subset_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (R p : ℝ) (hp : 1 ≤ p) (g : ℝ → E) (hg : ContDiff ℝ 1 g)
    (hsupp : tsupport g ⊆ ball 0 R) :
    eLpNorm g (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (2 * R) * eLpNorm (deriv g) (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
