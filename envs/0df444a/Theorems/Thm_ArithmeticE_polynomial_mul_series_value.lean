-- Prove2me | Theorems.Thm_ArithmeticE_polynomial_mul_series_value
-- name    : ArithmeticE.polynomial_mul_series_value
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T16:42:24.534212+00:00
-- url     : https://prove2.me/theorems/84803d38-8363-4cb6-bce1-ff9a0a22020a
-- title:
--   Polynomial multiplication commutes with canonical E-series evaluation
-- statement:
--   Let $f$ be a formal complex power series whose rational factorial-normalized coefficients satisfy the E-function exponential size and common-denominator bounds. For every complex polynomial $P$ and every $z\in\mathbb C$, canonical series evaluation obeys
--   $$\operatorname{value}(Pf,z)=P(z)\operatorname{value}(f,z).$$
--   This identifies the formal polynomial products used in scalar differential equations with their analytic values. The proof uses absolute convergence of the E-series, the finite support of the polynomial, and the Cauchy product formula. It needs no value-lifting or arithmetic zero theorem.
-- source:
--   Cauchy product theorem for absolutely convergent series; analytic identification needed in Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorem 3.2.

import Definitions.Def_rationalEArithmetic
open ArithmeticE

theorem ArithmeticE.polynomial_mul_series_value (P : Polynomial ℂ) (f : PowerSeries ℂ)
    (hf : RationalSeriesArithmetic f) (z : ℂ) :
    seriesValue ((P : PowerSeries ℂ)*f) z = P.eval z * seriesValue f z := by sorry
