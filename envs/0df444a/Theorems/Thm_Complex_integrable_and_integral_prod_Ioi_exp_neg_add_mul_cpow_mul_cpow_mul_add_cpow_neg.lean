-- Prove2me | Theorems.Thm_Complex_integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg
-- name    : Complex.integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/dea25ffa-cf42-5455-9616-077cfa45d84e
-- title:
--   Dirichlet double integral Γ(α+β-γ)Γ(α)Γ(β)/Γ(α+β)
-- statement:
--   Let $\alpha,\beta,\gamma$ be complex numbers with $\operatorname{Re}\alpha>0$, $\operatorname{Re}\beta>0$ and $\operatorname{Re}(\alpha+\beta-\gamma)>0$. Consider on $\mathbb{R}\times\mathbb{R}$ the function sending $p=(p_1,p_2)$ to $$e^{-(p_1+p_2)}\,p_1^{\,\alpha-1}\,p_2^{\,\beta-1}\,(p_1+p_2)^{-\gamma},$$ where the real arguments are coerced to $\mathbb{C}$ and the powers are the complex power function on $\mathbb{C}$, and equip $\mathbb{R}\times\mathbb{R}$ with the product of two copies of Lebesgue measure restricted to the open half-line $(0,\infty)$. The assertion is a conjunction: first, this function is integrable for that product measure; and second, its integral equals $$\frac{\Gamma(\alpha+\beta-\gamma)\,\Gamma(\alpha)\,\Gamma(\beta)}{\Gamma(\alpha+\beta)},$$ with $\Gamma$ the complex Gamma function of Mathlib. Thus absolute convergence of the double integral over the open quadrant and its evaluation in closed form are stated together, the second component being an equality in $\mathbb{C}$.
--
--   This is the Dirichlet-type double integral classically evaluated by passing to the coordinates $r=p_1+p_2$, $w=p_1/(p_1+p_2)$, which factors it as $\int_0^\infty e^{-r}r^{\alpha+\beta-\gamma-1}\,dr$ times the Euler Beta integral $B(\alpha,\beta)$. It is used in the archimedean Bessel computations, namely in [`LanglandsTunnell.ArchBessel.mellin_besselKernel_mul_besselKernel_eq`](thm.html#LanglandsTunnell.ArchBessel.mellin_besselKernel_mul_besselKernel_eq), to evaluate the Mellin transform of a product of two Bessel kernels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem Complex.integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg
    (α β γ : ℂ) (hα : 0 < α.re) (hβ : 0 < β.re) (hγ : 0 < (α + β - γ).re) :
    Integrable (fun p : ℝ × ℝ => Complex.exp (-(((p.1 + p.2 : ℝ)) : ℂ)) * (p.1 : ℂ) ^ (α - 1) *
        (p.2 : ℂ) ^ (β - 1) * (((p.1 + p.2 : ℝ)) : ℂ) ^ (-γ))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
      ∫ p : ℝ × ℝ, Complex.exp (-(((p.1 + p.2 : ℝ)) : ℂ)) * (p.1 : ℂ) ^ (α - 1) *
          (p.2 : ℂ) ^ (β - 1) * (((p.1 + p.2 : ℝ)) : ℂ) ^ (-γ)
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) =
        Complex.Gamma (α + β - γ) * Complex.Gamma α * Complex.Gamma β / Complex.Gamma (α + β) := by sorry
