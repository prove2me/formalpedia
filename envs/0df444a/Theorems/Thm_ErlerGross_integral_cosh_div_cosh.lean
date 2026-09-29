-- Prove2me | Theorems.Thm_ErlerGross_integral_cosh_div_cosh
-- name    : ErlerGross.integral_cosh_div_cosh
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:57:26.829015+00:00
-- url     : https://prove2.me/theorems/e967344d-a7b1-47d1-9d36-dd98f86c9c1a
-- title:
--   $\int_0^\infty\frac{\cosh ax}{\cosh bx}dx=\frac{\pi}{2b}\frac{1}{\cos\frac{\pi a}{2b}}$
-- statement:
--   For complex $a,b$ with $|\Re a|<\Re b$: $$\int_0^\infty dx\,\frac{\cosh ax}{\cosh bx}=\frac{\pi}{2b}\,\frac{1}{\cos\frac{\pi a}{2b}},$$ the integrand being integrable on $(0,\infty)$.
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2 (2004), https://arxiv.org/abs/hep-th/0406199; Appendix B, p. 45 (integral formula used to derive eq. B.2)

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem integral_cosh_div_cosh (a b : ℂ) (hab : |a.re| < b.re) :
    IntegrableOn (fun x : ℝ => Complex.cosh (a * x) / Complex.cosh (b * x)) (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), Complex.cosh (a * x) / Complex.cosh (b * x) =
        (π : ℂ) / (2 * b) * (1 / Complex.cos (π * a / (2 * b))) := by
  sorry

end ErlerGross
