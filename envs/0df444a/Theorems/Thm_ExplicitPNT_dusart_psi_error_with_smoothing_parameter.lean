-- Prove2me | Theorems.Thm_ExplicitPNT_dusart_psi_error_with_smoothing_parameter
-- name    : ExplicitPNT.dusart_psi_error_with_smoothing_parameter
-- status  : Open
-- author  : @abcdefg
-- created : 2026-10-09T15:48:03.058579+00:00
-- url     : https://prove2.me/theorems/0db4615e-792f-4664-bb94-2960c2249121
-- title:
--   Dusart intermediate Chebyshev psi estimate with a smoothing parameter
-- statement:
--   Let R > 0 and suppose the Riemann zeta function has no zeros with |Im(s)| > 2 pi and Re(s) > 1 - 1/(R log |Im(s)|). For x > 0, write X = sqrt(log x / R). If X > max(8.36, 8/R), there exists a real nu with 0.97 < nu < 1 such that
--
--   $$|\psi(x)-x| < x\sqrt{8/\pi}\sqrt X e^{-X} U^{1/4}\exp(5.91\sqrt X e^{-X}),$$
--
--   where
--
--   $$U=\frac{\nu^6}{2\nu^2-1}\left(1-\frac{\log(2\pi)-1/2}{X\nu}\right)\left(1-\frac{\log(2\pi)}{X\nu}\right).$$
--
--   This is the intermediate smoothing estimate in the proof of Dusart's Theorem 45. It is the remaining Open analytic obligation in the reduction of ExplicitPNT.dusart_refined_psi_error_of_zero_free_region. Its proof requires the explicit formula, estimates for sums over zeta zeros, and construction of the smoothing parameter. The subsequent numerical comparison is a separate proved auxiliary lemma.
-- source:
--   Pierre Dusart, Estimations explicites en Théorie Analytique des Nombres, Theorem 45 (printed p.37), proof on printed p.46; https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf . The smoothing estimate precedes the final comparison. The real inequality is an auxiliary generalization of that final comparison.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem ExplicitPNT.dusart_psi_error_with_smoothing_parameter
    (R : ℝ) (hR : 0 < R)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (x : ℝ) (hx : 0 < x)
    (hX : max (836 / 100 : ℝ) (8 / R) < Real.sqrt (Real.log x / R)) :
    let X := Real.sqrt (Real.log x / R)
    ∃ ν : ℝ, (97 / 100 : ℝ) < ν ∧ ν < 1 ∧
      |Chebyshev.psi x - x| <
        x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) *
          (Real.sqrt (Real.sqrt
            (ν ^ 6 / (2 * ν ^ 2 - 1) *
              (1 - (Real.log (2 * Real.pi) - 1 / 2) / (X * ν)) *
              (1 - Real.log (2 * Real.pi) / (X * ν)))) *
            Real.exp ((591 / 100 : ℝ) * Real.sqrt X * Real.exp (-X))) := by sorry
