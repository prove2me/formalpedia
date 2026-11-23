-- Prove2me | Theorems.Thm_BroughanRH_zagier
-- name    : BroughanRH.zagier
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:27:17.978937+00:00
-- url     : https://prove2.me/theorems/4a6cb6f9-090d-4132-969f-fdda3bb2cf55
-- title:
--   Zagier’s horocycle averages on the modular surface
-- statement:
--   For every smooth compactly supported function on the modular surface, the average along a closed horocycle at height $y$ differs from the normalized hyperbolic area mean by $o(y^{3/4-\varepsilon})$. The Lean coordinates impose invariance under the two modular generators. [Source](https://people.mpim-bonn.mpg.de/zagier/files/scanned/EisensteinRiemannZeta/fulltext.pdf).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §10.10 (smooth-test companion). https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem zagier :
    ∀ f : ℝ × ℝ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f {z | 0 < z.2} →
      (∀ x y : ℝ, 0 < y → f (x+1,y) = f (x,y)) →
      (∀ x y : ℝ, 0 < y → f (-x/(x^2+y^2),y/(x^2+y^2)) = f (x,y)) →
      (∃ Y : ℝ, 1 ≤ Y ∧ ∀ x y : ℝ, Y ≤ y → f (x,y) = 0) →
      let mean := (3/Real.pi) * (∫ x in (-(1/2 : ℝ))..(1/2 : ℝ),
        ∫ y in Set.Ici (Real.sqrt (1-x^2)), f (x,y)/y^2)
      ∀ ε : ℝ, 0 < ε → Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0))
        (fun y : ℝ => (∫ x in (0 : ℝ)..1, f (x,y)) - mean) (fun y : ℝ => y^(3/4-ε)) := by sorry

end BroughanRH
