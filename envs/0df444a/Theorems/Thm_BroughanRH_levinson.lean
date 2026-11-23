-- Prove2me | Theorems.Thm_BroughanRH_levinson
-- name    : BroughanRH.levinson
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:25:40.345923+00:00
-- url     : https://prove2.me/theorems/6d1ef9fa-fc57-44d6-990c-2c87ea14f047
-- title:
--   Levinson’s uniqueness test in a vertical strip
-- statement:
--   An $L^2$ function on the positive ray vanishes almost everywhere if all of its Levinson integrals vanish, for any admissible exponents and increasing parameter sequence with divergent reciprocal sum.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 8.15. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem levinson :
    ∀ u : ℕ → ℝ, u 0 = 1 → StrictMono u →
      Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (u j)⁻¹) Filter.atTop Filter.atTop →
      ∀ a b : ℝ, 1/2 < a → a < b → b < 1 →
      ∀ f : ℝ → ℂ, MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) →
      (∀ j : ℕ, (∫ x in Set.Ioi (0 : ℝ),
        (((x^(a-1/2) + x^(b-1/2))/(Real.exp (u j*x)+1) : ℝ) : ℂ)*f x) = 0) →
      ∀ᵐ x : ℝ ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), f x = 0 := by sorry

end BroughanRH
