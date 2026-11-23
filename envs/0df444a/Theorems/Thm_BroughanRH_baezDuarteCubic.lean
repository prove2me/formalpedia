-- Prove2me | Theorems.Thm_BroughanRH_baezDuarteCubic
-- name    : BroughanRH.baezDuarteCubic
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:20:51.301118+00:00
-- url     : https://prove2.me/theorems/38083627-b81b-4da8-9677-f016cbe4d117
-- title:
--   Báez-Duarte’s polynomial-exponential example
-- statement:
--   For $f(z)=(b_1 z+b_2 z^2+b_3 z^3)e^{-z}$ with $b_1\ne0$, suppose that $b_1s+b_2s(s+1)+b_3s(s+1)(s+2)$ has no zeros in $0<\operatorname{Re}s<1/2$. The transformed series satisfies the Báez-Duarte bound for every positive error exponent.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §2.5, Ex. 3 following Thm. 2.7. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem baezDuarteCubic :
    ∀ b₁ b₂ b₃ : ℂ, b₁ ≠ 0 →
      (∀ s : ℂ, 0 < s.re → s.re < 1/2 →
        b₁*s+b₂*s*(s+1)+b₃*s*(s+1)*(s+2) ≠ 0) →
      let f (z : ℂ) := (b₁*z+b₂*z^2+b₃*z^3)*Complex.exp (-z)
      ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop
        (fun x : ℝ => ∑' k : ℕ, (iteratedDeriv (k+1) f 0 / ((k+1).factorial : ℂ)) *
          (x : ℂ)^(k+1) / (((k+1 : ℕ) : ℂ) * riemannZeta ((k : ℂ)+2)))
        (fun x : ℝ => x^(-(1/2) + ε)) := by sorry

end BroughanRH
