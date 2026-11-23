-- Prove2me | Theorems.Thm_BroughanRH_nyman
-- name    : BroughanRH.nyman
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:21:00.968259+00:00
-- url     : https://prove2.me/theorems/b92a223c-0b51-4b1b-9963-8a1138071875
-- title:
--   Nyman’s approximation criterion
-- statement:
--   Finite linear combinations of the centered fractional-part kernels approximate every real square-integrable function on the unit interval in its $L^2$ norm.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 3.1. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem nyman :
    ∀ f : ℝ → ℝ, MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) →
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ a θ : Fin n → ℝ,
        (∀ j, θ j ∈ Set.Ioc 0 1) ∧ MeasureTheory.eLpNorm
          (fun x : ℝ => f x - ∑ j, a j * (Int.fract (θ j / x) - θ j * Int.fract (1 / x)))
          2 (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) < ENNReal.ofReal ε := by sorry

end BroughanRH
