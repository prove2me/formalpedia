-- Prove2me | Theorems.Thm_ExplicitPNT_dusart_refined_psi_error_of_zero_free_region
-- name    : ExplicitPNT.dusart_refined_psi_error_of_zero_free_region
-- status  : Open
-- author  : @abcdefg
-- created : 2026-10-09T14:30:14.498028+00:00
-- url     : https://prove2.me/theorems/ca6e6537-f735-46a4-bcc2-5d26b8e72abe
-- title:
--   Dusart's refined ψ error envelope from a classical zero-free region
-- statement:
--   Let $R>0$ be such that the Riemann zeta function has no zeros in
--   $$\sigma>1-\frac{1}{R\log|t|},\qquad |t|>2\pi.$$
--   For $x>0$, put $X=\sqrt{\log x/R}$ and suppose
--   $$X>\max(8.36,8/R).$$
--   Then the Chebyshev function $\psi(x)=\sum_{n\le x}\Lambda(n)$ satisfies
--   $$|\psi(x)-x|<
--   x\sqrt{\frac8\pi}\,X^{1/2}e^{-X}
--   \left(1-\frac{\log(2\pi)-1/2}{X}\right)^{1/4}.$$
--
--   This is the sharper envelope obtained at the end of Dusart's proof of Théorème 45. Its extra factor retains a margin that can absorb the contribution of prime powers when passing from $\psi$ to $\vartheta$. The zero-free-region hypothesis is explicit; the analytic explicit-formula, zero-counting and low-height zero estimates remain part of this theorem's proof obligation.
--
--   **Formalization Note** The fourth root is represented by two nested nonnegative real square roots. The threshold ensures its argument is positive.
-- source:
--   P. Dusart, Estimations explicites en Théorie Analytique des Nombres (HDR, 2022), Théorème 45, printed p.37, proof printed p.46, final displayed refined ε(x) envelope; https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf (PDF pp.47 and 56). Restates the proof of Theorem 1.1 in Math. Comp. 85 (2016), 875–888, DOI 10.1090/S0025-5718-2015-03005-1.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem ExplicitPNT.dusart_refined_psi_error_of_zero_free_region
    (R : ℝ) (hR : 0 < R)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (x : ℝ) (hx : 0 < x)
    (hX : max (836 / 100 : ℝ) (8 / R) < Real.sqrt (Real.log x / R)) :
    |Chebyshev.psi x - x| <
      x * Real.sqrt (8 / Real.pi) * Real.sqrt (Real.sqrt (Real.log x / R)) *
        Real.exp (-Real.sqrt (Real.log x / R)) *
        Real.sqrt (Real.sqrt
          (1 - (Real.log (2 * Real.pi) - 1 / 2) / Real.sqrt (Real.log x / R))) := by sorry
