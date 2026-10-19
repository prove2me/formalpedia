-- Prove2me | Theorems.Thm_ExplicitPNT_dusart_k_root_exists
-- name    : ExplicitPNT.dusart_k_root_exists
-- status  : Proved
-- author  : @chaikon
-- created : 2026-10-14T03:05:06.285708+00:00
-- url     : https://prove2.me/theorems/137b1ff1-a2e6-4e2c-98c2-04875ae996c1
-- title:
--   Dusart, Lemme 51: the root of $k(\nu)=1$ lies in $(0.97,1)$
-- statement:
--   Fix $X\ge 8.36$ and, for $\nu\in(1/\sqrt2,1]$, put (Dusart's (2.18) and (2.38), i.e. (2.25) with $m=2$)
--   $$G_0(\nu)=\nu^2\Bigl(\nu-\frac{\log(2\pi)}{X}\Bigr),\qquad G_1(\nu)=\frac{\nu^2}{2\nu^2-1}\Bigl(\nu+\frac{1-2\log(2\pi)}{2X}\Bigr),$$
--   and (2.32)
--   $$k(\nu)=\frac{X}{2\pi}\Bigl(\frac{G_0^3}{G_1}\Bigr)^{1/2}e^{-2X(1-\nu)}\,e^{-X(1-\nu)^2/\nu}.$$
--   Then there is a real $\nu$ with $k(\nu)=1$ and
--   $$0.97<1-\frac{1}{2X}\log\frac{X}{2\pi}<\nu<1 .$$
--
--   This is Lemme 51 of Dusart's habilitation (display (2.39)). The proof there: for $\nu\in(1/\sqrt2,1]$, $G_0$ increases and $G_1$ decreases, so $k$ is increasing; $k(\nu)\to0$ as $\nu\to1/\sqrt2^{+}$ and $k(1)>1$ exactly when $X$ exceeds $\frac{\sqrt3}{3}\bigl(4\pi\cos(\frac13\arctan\sqrt{(8\pi)^2/27-1})+\sqrt3\log(2\pi)\bigr)\approx8.358$; finally $k(\nu_0)<1$ at $\nu_0=1-\frac1{2X}\log\frac X{2\pi}$, whose minimum over $X$ is $1-\frac1{4\pi e}\approx0.9707$, attained at $X=2\pi e$. The root $\nu$ is the smoothing parameter of the proof of Théorème 45.
--
--   **Formalization note.** $(G_0^3/G_1)^{1/2}$ is `Real.sqrt` of the quotient, which is positive in the relevant range. The statement only needs existence; uniqueness, also proved in the source, is not asserted.
-- source:
--   P. Dusart, Estimations explicites en Théorie Analytique des Nombres (HDR, 2022), Lemme 51, display (2.39), printed p. 43 (PDF p. 53), with k, G0, G1 from (2.18), (2.32), (2.38) on printed pp. 38-43; https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf . Same argument as Dusart, Math. Comp. 85 (2016), 875-888, and Schoenfeld, Math. Comp. 30 (1976), (7.27) p. 345.

import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem ExplicitPNT.dusart_k_root_exists (X : ℝ) (hX : (836 / 100 : ℝ) ≤ X) :
    ∃ ν : ℝ,
      (97 / 100 : ℝ) < 1 - Real.log (X / (2 * Real.pi)) / (2 * X) ∧
      1 - Real.log (X / (2 * Real.pi)) / (2 * X) < ν ∧ ν < 1 ∧
      X / (2 * Real.pi) *
          Real.sqrt ((ν ^ 2 * (ν - Real.log (2 * Real.pi) / X)) ^ 3 /
            (ν ^ 2 / (2 * ν ^ 2 - 1) *
              (ν + (1 - 2 * Real.log (2 * Real.pi)) / (2 * X)))) *
          Real.exp (-(2 * X * (1 - ν))) * Real.exp (-(X * (1 - ν) ^ 2 / ν)) = 1 := by
  sorry
