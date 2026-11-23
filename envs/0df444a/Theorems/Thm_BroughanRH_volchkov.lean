-- Prove2me | Theorems.Thm_BroughanRH_volchkov
-- name    : BroughanRH.volchkov
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:25:36.978307+00:00
-- url     : https://prove2.me/theorems/fb90409a-54df-4559-b62f-bcc00b98dbe3
-- title:
--   Volchkov’s double integral of the zeta log modulus
-- statement:
--   Volchkov’s iterated integral over $t>0$ and $\sigma>1/2$ equals $\pi(3-\gamma)/32$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 8.10. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem volchkov :
    let f (t : ℝ) := (1-12*t^2)/(1+4*t^2)^3 *
      (∫ σ in Set.Ioi (1/2 : ℝ), Real.log ‖riemannZeta ((σ : ℂ)+(t : ℂ)*Complex.I)‖)
    MeasureTheory.IntegrableOn f (Set.Ioi 0) ∧ (∫ t in Set.Ioi (0 : ℝ), f t) =
      (Real.pi/32)*(3-Real.eulerMascheroniConstant) := by sorry

end BroughanRH
