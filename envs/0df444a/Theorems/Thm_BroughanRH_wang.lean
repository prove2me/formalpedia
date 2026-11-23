-- Prove2me | Theorems.Thm_BroughanRH_wang
-- name    : BroughanRH.wang
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:24:44.329568+00:00
-- url     : https://prove2.me/theorems/8ad78be3-a453-4d38-b292-7179d6c7f8b7
-- title:
--   Wang’s integral on the critical line
-- statement:
--   The integral of $t^{-2}\log|\zeta(1/2+it)|$ over $t\geq1$ equals Wang’s arc integral. On the arc the branch of $\log\zeta$ is obtained from the right, taking its real value at $3/2$. [Source](https://doi.org/10.1090/S0002-9904-1946-08569-9).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §8.1. https://doi.org/10.1090/S0002-9904-1946-08569-9

import Mathlib

namespace BroughanRH

theorem wang :
    let H (b t : ℝ) : ℂ := -(∫ u in Set.Ioi b, deriv riemannZeta ((u : ℂ)+(t : ℂ)*Complex.I) / riemannZeta ((u : ℂ)+(t : ℂ)*Complex.I))
    let f (t : ℝ) := Real.log ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*Complex.I)‖ / t^2
    let g (θ : ℝ) := (Complex.exp (-(θ : ℂ)*Complex.I) * H (1/2 + Real.cos θ) (Real.sin θ)).re
    (∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi/2), MeasureTheory.IntegrableOn
      (fun u : ℝ => deriv riemannZeta ((u : ℂ)+(Real.sin θ : ℂ)*Complex.I) /
        riemannZeta ((u : ℂ)+(Real.sin θ : ℂ)*Complex.I)) (Set.Ioi (1/2+Real.cos θ))) ∧
    IntervalIntegrable g MeasureTheory.volume 0 (Real.pi/2) ∧ MeasureTheory.IntegrableOn f (Set.Ioi 1) ∧
      (∫ t in Set.Ioi (1 : ℝ), f t) = ∫ θ in (0 : ℝ)..(Real.pi/2), g θ := by sorry

end BroughanRH
