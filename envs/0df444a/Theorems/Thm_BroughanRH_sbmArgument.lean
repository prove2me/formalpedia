-- Prove2me | Theorems.Thm_BroughanRH_sbmArgument
-- name    : BroughanRH.sbmArgument
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:25:16.659466+00:00
-- url     : https://prove2.me/theorems/af48484f-e820-43e3-ad36-9825804209b6
-- title:
--   The weighted zeta-argument identity
-- statement:
--   Integrate the horizontal-branch zeta argument over positive heights with weight $t/((1-b)^2+t^2)^2$, for $1/2<b<1$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Cor. 8.9. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem sbmArgument :
    let h (b t : ℝ) : ℂ := -(∫ u in Set.Ioi b, deriv riemannZeta ((u : ℂ) + (t : ℂ)*Complex.I) / riemannZeta ((u : ℂ) + (t : ℂ)*Complex.I))
    ∀ b : ℝ, 1/2 < b → b < 1 →
      let f (t : ℝ) := t*(h b t).im/((1-b)^2+t^2)^2
      MeasureTheory.IntegrableOn f (Set.Ioi 0) ∧ (∫ t in Set.Ioi (0 : ℝ), f t) =
      Real.pi*Real.eulerMascheroniConstant/(4*(1-b)) - 3*Real.pi/(8*(1-b)^2) := by sorry

end BroughanRH
