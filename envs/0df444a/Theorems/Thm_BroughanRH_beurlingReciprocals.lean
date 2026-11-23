-- Prove2me | Theorems.Thm_BroughanRH_beurlingReciprocals
-- name    : BroughanRH.beurlingReciprocals
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:21:15.67316+00:00
-- url     : https://prove2.me/theorems/2196b255-6ac8-4f05-93b0-de061faecd65
-- title:
--   Approximation by reciprocal-integer fractional parts
-- statement:
--   The indicator of $(0,1]$ can be approximated in $L^2(0,\infty)$ using finite real linear combinations of the functions $x\mapsto\{1/(nx)\}$ for positive integers $n$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §3.4 (Báez-Duarte). https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem beurlingReciprocals :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℝ,
      MeasureTheory.eLpNorm (fun x : ℝ =>
        (if x ∈ Set.Ioc 0 1 then (1 : ℝ) else 0) -
        ∑ j, a j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x)))
        2 (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) < ENNReal.ofReal ε := by sorry

end BroughanRH
