-- Prove2me | Theorems.Thm_BroughanRH_amoroso
-- name    : BroughanRH.amoroso
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:24:49.276345+00:00
-- url     : https://prove2.me/theorems/f9a750d4-b4d0-4de9-aebe-897a762e3221
-- title:
--   Amoroso’s height bound for products of cyclotomic polynomials
-- statement:
--   For the product of the first $N$ cyclotomic polynomials, the circle average of its positive log modulus is $O_\varepsilon(N^{1/2+\varepsilon})$ for every $\varepsilon>0$. [Source](https://iris.unito.it/retrieve/705ad352-d769-4f7e-aa39-0906d74ed201/M.pdf).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §7.4. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem amoroso :
    let F (N : ℕ) := ∏ j ∈ Finset.Icc 1 N, Polynomial.cyclotomic j ℂ
    let h (N : ℕ) : ℝ := (∫ t in (-Real.pi)..Real.pi, max 0
      (Real.log ‖(F N).eval (Complex.exp ((t : ℂ) * Complex.I))‖)) / (2 * Real.pi)
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop h (fun N : ℕ => (N : ℝ)^(1/2+ε)) := by sorry

end BroughanRH
