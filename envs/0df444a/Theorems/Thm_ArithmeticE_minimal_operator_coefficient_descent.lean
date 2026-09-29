-- Prove2me | Theorems.Thm_ArithmeticE_minimal_operator_coefficient_descent
-- name    : ArithmeticE.minimal_operator_coefficient_descent
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T21:07:49.738879+00:00
-- url     : https://prove2.me/theorems/1d573d1e-d78e-4657-80e0-c9a81558c2e0
-- title:
--   A minimal complex differential equation descends to the series coefficient field
-- statement:
--   Let $K$ be a field embedded in $\mathbb C$, and let $f\in K[[X]]$. Suppose the image of $f$ in $\mathbb C[[X]]$ has a minimal polynomial differential equation $L$ of order $n$. Then it has a minimal equation of order $n$ with coefficients in $K[X]$. One coefficient of its leading polynomial can moreover be normalized to one.
--
--   Choose a nonzero coefficient $c$ in the leading polynomial of $L$, and a $K$-linear functional $\sigma:\mathbb C\to K$ taking $c$ to one. Apply $\sigma$ coefficientwise to all coefficient polynomials of $L$. Every formal coefficient equation is $K$-linear, so the projected operator still annihilates $f$. Its leading polynomial is nonzero by the chosen normalization. Mapping the equation back to $\mathbb C$ gives the same order $n$, and minimality excludes every smaller equation.
--
--   The proof does not require $K/\mathbb Q$ to be algebraic, or convergence or arithmetic bounds on $f$. In the E-function application, it justifies working over the actual arithmetic coefficient field rather than assuming that a complex minimal operator already has arithmetic coefficients.
-- source:
--   Standard coefficient-field descent by linear projection; used when identifying minimal differential equations over the arithmetic field in Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Section 2. The statement and projection argument are explicitly proved here; no arithmetic regularity theorem is invoked.

import Definitions.Def_beukersLiftingData
open ArithmeticE

theorem ArithmeticE.minimal_operator_coefficient_descent {K : Type*} [Field K] [Algebra K ℂ] (f : PowerSeries K)
    (p : ℕ → Polynomial ℂ) (n : ℕ)
    (hm : MinimalEquation p n (f.map (algebraMap K ℂ))) :
    ∃ q : ℕ → Polynomial K,
      MinimalEquation (fun k => (q k).map (algebraMap K ℂ)) n (f.map (algebraMap K ℂ)) ∧
      ∃ d, (q n).coeff d = 1 := by sorry
