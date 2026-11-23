-- Prove2me | Theorems.Thm_BroughanRH_sbmPoisson
-- name    : BroughanRH.sbmPoisson
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:25:03.570294+00:00
-- url     : https://prove2.me/theorems/13be815c-92d7-41b4-b385-d41fe9e9dd50
-- title:
--   The Poisson-weighted log-modulus identity
-- statement:
--   Sekatskii, Beltraminelli and Merlini’s two-parameter identity holds for $a>0$, $1/2\le b<1$ and $a+b\ne1$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Lemma 8.5. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem sbmPoisson :
    ∀ a b : ℝ, 0 < a → 1/2 ≤ b → b < 1 → a+b ≠ 1 →
      let f (t : ℝ) := Real.log ‖riemannZeta ((b : ℂ)+(t : ℂ)*Complex.I)‖/(a^2+t^2)
      MeasureTheory.Integrable f ∧ (a/Real.pi)*(∫ t : ℝ, f t) =
      Real.log ‖riemannZeta ((a+b : ℝ) : ℂ) * ((a+b-1)/(a-b+1) : ℝ)‖ := by sorry

end BroughanRH
