-- Prove2me | Theorems.Thm_BanditAlgorithm_pair_weight_superadditive
-- name    : BanditAlgorithm.pair_weight_superadditive
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T04:17:27.432481+00:00
-- url     : https://prove2.me/theorems/19932d10-28b6-4f2f-a34e-f7a1ab89025b
-- title:
--   Superadditivity of the pair weight $\tfrac{xy}{x+y}$
-- statement:
--   For positive reals $x_1,y_1,x_2,y_2$,
--   $$\frac{x_1y_1}{x_1+y_1}+\frac{x_2y_2}{x_2+y_2}\ \le\ \frac{(x_1+x_2)(y_1+y_2)}{(x_1+x_2)+(y_1+y_2)}.$$
--
--   The function $h(x,y)=xy/(x+y)$ is half the harmonic mean, characterised by $1/h=1/x+1/y$; in electrical language it is the resistance of two resistors in parallel, and the inequality says that thickening both branches of a parallel pair is at least as good as running the two pairs separately. Since $h$ is positively homogeneous of degree one, superadditivity is equivalent to concavity on the open quadrant, so this is the concavity of $h$ in the form that avoids mentioning convex combinations.
--
--   Clearing denominators reduces the claim to $(x_1y_2-x_2y_1)^2\ge0$: writing $D$ for the difference of the two sides multiplied by $(x_1+y_1)(x_2+y_2)\big((x_1+x_2)+(y_1+y_2)\big)$, one has the polynomial identity $D=(x_1y_2-x_2y_1)^2$. So the inequality and the description of its equality case come from a single computation.
--
--   In the best-arm-identification application $h(\alpha_i,\alpha_j)$ is the effective sample size of the pair $(i,j)$ under an allocation $\alpha$, and concavity of the objective $\min_{j\ne i}h(\alpha_i,\alpha_j)(\mu_i-\mu_j)^2/2$ is what makes the set of optimal allocations convex.
-- source:
--   Superadditivity of the parallel sum (harmonic mean) of positive reals; used for the concavity of the best-arm-identification allocation objective of Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Eq. (33.4).

import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem BanditAlgorithm.pair_weight_superadditive {x₁ y₁ x₂ y₂ : ℝ}
    (hx₁ : 0 < x₁) (hy₁ : 0 < y₁) (hx₂ : 0 < x₂) (hy₂ : 0 < y₂) :
    x₁ * y₁ / (x₁ + y₁) + x₂ * y₂ / (x₂ + y₂)
      ≤ (x₁ + x₂) * (y₁ + y₂) / ((x₁ + x₂) + (y₁ + y₂)) := by
  sorry
