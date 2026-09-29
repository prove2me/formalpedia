-- Prove2me | Theorems.Thm_ArithmeticE_rational_series_division
-- name    : ArithmeticE.rational_series_division
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:57:16.901853+00:00
-- url     : https://prove2.me/theorems/0f721b1b-462b-4715-a96e-ecd6722c8f26
-- title:
--   Constructive arithmetic division of a rational E-series by one minus X
-- statement:
--   Suppose rational normalized coefficients $a_n$ satisfy exponential size and common-denominator bounds and $\sum_{n\ge0}a_n/n!=0$. Put $f(X)=\sum_n a_nX^n/n!$. There exists a formal series $g$ satisfying the same rational E-arithmetic coefficient conditions and
--   $$(1-X)g(X)=f(X).$$
--   The coefficient of $X^n$ in $g$ is the partial sum $\sum_{k\le n}a_k/k!$. The theorem proves the arithmetic condition and formal division identity; holonomicity is not part of the arithmetic predicate.
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, proof of Corollary 2.2, pp. 3–4. This formalization proves the rational arithmetic division step without invoking André or Beukers specialization.

import Definitions.Def_rationalEArithmetic
open ArithmeticE

theorem ArithmeticE.rational_series_division (a : ℕ → ℚ) (ha : RationalArithmetic a)
    (hz : HasSum (fun n : ℕ => (a n:ℝ)/(n.factorial:ℝ)) 0) :
    ∃ g : PowerSeries ℂ, RationalSeriesArithmetic g ∧
      (1-PowerSeries.X)*g = PowerSeries.mk (fun n => (a n:ℂ)/(n.factorial:ℂ)) := by sorry
