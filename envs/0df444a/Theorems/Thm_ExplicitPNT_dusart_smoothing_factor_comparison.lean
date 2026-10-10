-- Prove2me | Theorems.Thm_ExplicitPNT_dusart_smoothing_factor_comparison
-- name    : ExplicitPNT.dusart_smoothing_factor_comparison
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T15:48:09.06836+00:00
-- url     : https://prove2.me/theorems/70a6fffa-7d90-4d54-a79e-3018c231831f
-- title:
--   Dusart smoothing multiplier is below the refined fourth-root envelope
-- statement:
--   Let X, nu, L be real numbers with X >= 8, 0.97 <= nu < 1, and 1.5 <= L <= 7. Then
--
--   $$\left[\frac{\nu^6}{2\nu^2-1}\left(1-\frac{L-1/2}{X\nu}\right)\left(1-\frac L{X\nu}\right)\right]^{1/4}\exp(5.91\sqrt X e^{-X}) < \left(1-\frac{L-1/2}{X}\right)^{1/4}.$$
--
--   Fourth roots are represented by two successive nonnegative real square roots. This is a real-variable auxiliary lemma for the final numerical step in the refined Dusart Chebyshev estimate. For the application, take L = log(2 pi). It requires no analytic number theory hypothesis. A complete Lean proof uses a positive polynomial factorization and the sixth Taylor term of the exponential.
-- source:
--   Pierre Dusart, Estimations explicites en Théorie Analytique des Nombres, Theorem 45 (printed p.37), proof on printed p.46; https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf . The smoothing estimate precedes the final comparison. The real inequality is an auxiliary generalization of that final comparison.

import Mathlib

theorem ExplicitPNT.dusart_smoothing_factor_comparison (X ν L : ℝ)
    (hX : 8 ≤ X) (hν : 97 / 100 ≤ ν) (hν1 : ν < 1)
    (hL : 3 / 2 ≤ L) (hL7 : L ≤ 7) :
    Real.sqrt (Real.sqrt
      (ν ^ 6 / (2 * ν ^ 2 - 1) *
        (1 - (L - 1 / 2) / (X * ν)) * (1 - L / (X * ν)))) *
      Real.exp ((591 / 100 : ℝ) * Real.sqrt X * Real.exp (-X)) <
        Real.sqrt (Real.sqrt (1 - (L - 1 / 2) / X)) := by sorry
