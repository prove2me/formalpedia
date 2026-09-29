-- Prove2me | Theorems.Thm_AnalyticGeometry_exists_poly_unique_zero
-- name    : AnalyticGeometry.exists_poly_unique_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T13:56:29.953555+00:00
-- url     : https://prove2.me/theorems/5c16cdb4-2d73-443c-af72-878e2d4b2e7a
-- title:
--   A polynomial in $1 + T^n\mathbb{R}[T]$ whose only zero in $\{0<|y|\le r\}$ is $x$
-- statement:
--   Let $0 < x \le r < 1$ and let $n$ be a natural number. There is a real polynomial
--   $$g \in 1 + T^n\,\mathbb{R}[T]$$
--   — that is, with constant term $1$ and vanishing coefficients in degrees $1, \dots, n-1$ — whose only
--   zero in the punctured closed disc $\{\, y \in \mathbb{C} : 0 < |y| \le r \,\}$ is $y = x$.
--
--   This is the inductive construction in case (1) of Theorem 7.1 of the source: one starts from
--   $g_1 = 1 - x^{-1}T$ and passes from $g_n = 1 + a_n T^n + \dots$ to
--   $g_{n+1} = g_n\big(1 - \tfrac{a_n}{m} T^n\big)^m$ for an integer $m > |a_n|$, whose extra zeros have
--   modulus $(m/|a_n|)^{1/n} > 1 > r$ and so stay outside the disc. Pushing $n$ up is what later allows
--   a correction factor with small coefficients to turn $g$ into a series with integer coefficients.
-- source:
--   Peter Scholze (all results joint with Dustin Clausen), Lectures on Analytic Geometry, Lecture VII, pp. 42-44, Theorem 7.1 (attributed there to D. Harbater, Convergent arithmetic power series, Amer. J. Math. 106 (1984), 801-846). https://www.math.uni-bonn.de/people/scholze/Analytic.pdf

import Mathlib
import Definitions.Def_AnalyticGeometry_ZLaurentGT

namespace AnalyticGeometry

/-- For every `n` there is a real polynomial `g ∈ 1 + Tⁿ ℝ[T]` whose only zero in the
punctured closed disc `{0 < |y| ≤ r}` is `x`. -/
theorem exists_poly_unique_zero (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hx0 : 0 < x)
    (hxr : x ≤ r) (n : ℕ) :
    ∃ g : Polynomial ℝ, g.coeff 0 = 1 ∧ (∀ i : ℕ, 0 < i → i < n → g.coeff i = 0) ∧
      ∀ y : ℂ, 0 < ‖y‖ → ‖y‖ ≤ r →
        (Polynomial.aeval y g = 0 ↔ y = (x : ℂ)) := by
  sorry

end AnalyticGeometry
