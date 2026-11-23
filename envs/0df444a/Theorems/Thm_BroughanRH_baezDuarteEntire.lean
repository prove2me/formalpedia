-- Prove2me | Theorems.Thm_BroughanRH_baezDuarteEntire
-- name    : BroughanRH.baezDuarteEntire
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:20:50.599468+00:00
-- url     : https://prove2.me/theorems/1343e42a-1ff1-4a3e-a62f-f74fe3ca899e
-- title:
--   Báez-Duarte’s entire-function series criterion
-- statement:
--   For each entire function vanishing at zero and satisfying the stated weighted-integrability and nonvanishing Mellin-transform conditions, its modified Taylor series is $O_\varepsilon(x^{-1/2+\varepsilon})$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 2.7. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem baezDuarteEntire :
    ∀ f : ℂ → ℂ, Differentiable ℂ f → f 0 = 0 →
      (∀ σ : ℝ, -(1/2) < σ → σ < 0 → MeasureTheory.IntegrableOn
        (fun t : ℝ => t^(-σ-1) * ‖f (t : ℂ)‖) (Set.Ioi 0)) →
      (∀ s : ℂ, -(1/2) < s.re → s.re < 0 →
        (∫ t in Set.Ioi (0 : ℝ), (t : ℂ)^(-s-1) * f (t : ℂ)) ≠ 0) →
      ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop
        (fun x : ℝ => ∑' k : ℕ, (iteratedDeriv (k+1) f 0 / ((k+1).factorial : ℂ)) *
          (x : ℂ)^(k+1) / (((k+1 : ℕ) : ℂ) * riemannZeta ((k : ℂ)+2)))
        (fun x : ℝ => x^(-(1/2) + ε)) := by sorry

end BroughanRH
