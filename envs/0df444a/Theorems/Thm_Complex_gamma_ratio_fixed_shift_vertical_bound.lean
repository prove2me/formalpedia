-- Prove2me | Theorems.Thm_Complex_gamma_ratio_fixed_shift_vertical_bound
-- name    : Complex.gamma_ratio_fixed_shift_vertical_bound
-- status  : Proved
-- author  : @GeorgeCoote
-- created : 2026-11-21T20:10:34.195429+00:00
-- url     : https://prove2.me/theorems/20e39f57-31ae-4b78-a16b-0300ee00fb9a
-- title:
--   Sharp Gamma-ratio bound at oppositely directed, shifted heights
-- statement:
--   Fix real numbers $a,b,u,v$ and $k>0$. There are constants $C\ge 0$ and $T\ge 1$ such that for all real $t$ with $|t|\ge T$,
--   $$
--   \left|\frac{\Gamma(a+i(u-kt))}{\Gamma(b+i(v+kt))}\right|
--   \le C|t|^{a-b}.
--   $$
--
--   The two-sided fixed-line Stirling asymptotic bounds the Gamma moduli above and below by constant multiples of $|y|^{x-1/2}e^{-\pi|y|/2}$ for large $|y|$, at each fixed real part $x$. Both $|u-kt|$ and $|v+kt|$ are comparable to $|t|$, so the ratio of the power terms is bounded by a constant times $|t|^{a-b}$, for arbitrary signs of the exponents. The difference between the two absolute heights has absolute value at most $|u+v|$ by the reverse triangle inequality. This bounds the ratio of the exponential terms uniformly.
-- source:
--   NIST Digital Library of Mathematical Functions, §5.11(i), equation (5.11.9), https://dlmf.nist.gov/5.11.E9. Fixed-line ratio consequence used in A. M. Masullo, The Music of the Primes (20 November 2026), pp. 590–591, (B.1.1.10).

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

theorem Complex.gamma_ratio_fixed_shift_vertical_bound
    (a b u v k : ℝ) (hk : 0 < k) :
    ∃ C T : ℝ, 0 ≤ C ∧ 1 ≤ T ∧
      ∀ (t : ℝ) (z w : ℂ), T ≤ |t| →
        z.re = a → w.re = b → z.im = u - k * t → w.im = v + k * t →
        ‖Complex.Gamma z / Complex.Gamma w‖ ≤ C * |t| ^ (a - b) := by sorry
