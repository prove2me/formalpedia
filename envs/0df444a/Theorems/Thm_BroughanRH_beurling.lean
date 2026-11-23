-- Prove2me | Theorems.Thm_BroughanRH_beurling
-- name    : BroughanRH.beurling
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:21:05.728007+00:00
-- url     : https://prove2.me/theorems/36a0ce7a-3c31-41a4-8a8c-cca34e884e64
-- title:
--   Beurling’s constrained approximation at exponent two
-- statement:
--   In the $p=2$ case of Beurling’s theorem, the finite linear combinations with $\sum_j a_j\theta_j=0$ are dense in real $L^2(0,1)$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 3.6. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem beurling :
    ∀ f : ℝ → ℝ, MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) →
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ a θ : Fin n → ℝ,
        (∀ j, θ j ∈ Set.Ioc 0 1) ∧ (∑ j, a j * θ j) = 0 ∧
        MeasureTheory.eLpNorm (fun x : ℝ => f x - ∑ j, a j * Int.fract (θ j / x))
          2 (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) < ENNReal.ofReal ε := by sorry

end BroughanRH
