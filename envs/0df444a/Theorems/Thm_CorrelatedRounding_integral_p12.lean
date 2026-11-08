-- Prove2me | Theorems.Thm_CorrelatedRounding_integral_p12
-- name    : CorrelatedRounding.integral_p12
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:34:38.784898+00:00
-- url     : https://prove2.me/theorems/56126e81-58c5-4521-90a7-229a07279f14
-- title:
--   Proof of Theorem 1, p.12 — the integral equals $1+\ln q$
-- statement:
--   For every integer $q\ge1$,
--   $$\int_0^\infty\min\{qe^{-t},1\}\,dt=\ln q+\int_{\ln q}^\infty qe^{-t}\,dt=\ln q+qe^{-\ln q}=1+\ln q .$$
--   This elementary integral is the source of the constant $1+\ln q$ in Theorem 1.
--
--   Differences from the source: none.
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, proof of Theorem 1, display, p.12

import Mathlib

namespace CorrelatedRounding

/-- **The elementary integral.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4, proof of Theorem 1, p.12:
"∫_0^∞ min{q e^{−t}, 1} dt = ln(q) + ∫_{ln(q)}^∞ q e^{−t} dt = ln(q) + q e^{−ln(q)} = 1 + ln(q)."

**Formalization Note.** The three equalities of the chain are the three conjuncts. For `q ≥ 1` the integrands
are integrable, so the Bochner integrals are the true values (the value `1 + ln q ≠ 0` of the first integral
in any case rules out the junk value `0`). -/
theorem integral_p12 (q : ℕ) (hq : 1 ≤ q) :
    (∫ t in Set.Ioi (0 : ℝ), min ((q : ℝ) * Real.exp (-t)) 1) =
        Real.log q + ∫ t in Set.Ioi (Real.log q), (q : ℝ) * Real.exp (-t) ∧
      Real.log q + (∫ t in Set.Ioi (Real.log q), (q : ℝ) * Real.exp (-t)) =
        Real.log q + q * Real.exp (-Real.log q) ∧
      Real.log q + q * Real.exp (-Real.log q) = 1 + Real.log q := by sorry

end CorrelatedRounding
