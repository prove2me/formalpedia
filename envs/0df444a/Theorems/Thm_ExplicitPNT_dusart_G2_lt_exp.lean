-- Prove2me | Theorems.Thm_ExplicitPNT_dusart_G2_lt_exp
-- name    : ExplicitPNT.dusart_G2_lt_exp
-- status  : Open
-- author  : @chaikon
-- created : 2026-10-14T03:05:08.102433+00:00
-- url     : https://prove2.me/theorems/faac22d1-ea50-43d3-9c30-62f3ae9676b2
-- title:
--   Dusart, Lemme 55: $G_2<\exp(2.64\,X^{1/2}e^{-X})$
-- statement:
--   Let $X>8.36$ and let $0.97<\nu<1$ be a root of $k(\nu)=1$, where $k$, $G_0$, $G_1$ are as in Dusart's (2.18), (2.32), (2.38) (see `ExplicitPNT.dusart_k_root_exists`). With $m=2$ put
--   $$Y=\frac{X(1-\nu)^2}{\nu},\qquad T_2=e^{\nu X},\qquad \delta=\sqrt{\tfrac2\pi}\,(G_0G_1)^{1/4}e^{-Y/2}X^{1/2}e^{-X},$$
--   $$q(y)=\frac{0.137\log y+0.443}{y\log y\,\log(y/2\pi)},\qquad G_2=\frac{R_2(\delta)}{2^2}\bigl(1+2\pi q(T_2)\bigr),\quad R_2(\delta)=\bigl((1+\delta)^3+1\bigr)^2,$$
--   where
--   $$G_0G_1=\frac{\nu^6}{2\nu^2-1}\Bigl(1-\frac{\log(2\pi)-1/2}{X\nu}\Bigr)\Bigl(1-\frac{\log(2\pi)}{X\nu}\Bigr).$$
--   Then
--   $$G_2<\exp\bigl(2.64\,X^{1/2}e^{-X}\bigr).$$
--
--   This is Lemme 55 of Dusart's habilitation, display (2.43). Proof in the source: by Lemme 52, $(G_0G_1)^{1/4}<1$ and $e^{-Y/2}\le1$, so $\delta<\sqrt{2/\pi}X^{1/2}e^{-X}$, whence $R_2(\delta)/4=(1+\tfrac12\delta(3+3\delta+\delta^2))^2<\exp(3.01122\,\delta)<\exp(2.41X^{1/2}e^{-X})$. Since $k(\nu)=1$, $T_2=e^{\nu X}$ coincides with (2.33), so $2\pi/T_2=\sqrt{2\pi}(G_0^3/G_1)^{1/4}e^{-Y/2}X^{1/2}e^{-X}$ and, using $G_0^3/G_1<1$ (2.41), $1+2\pi q(T_2)<1+0.23X^{1/2}e^{-X}<\exp(0.23X^{1/2}e^{-X})$. Multiply.
--
--   **Formalization note.** The source states the lemma for $X>2\pi$, $\nu>1/\sqrt2$ with $k(\nu)=1$, but its proof uses the bounds of Lemme 52, proved under $X>8.36$ and $0.97<\nu<1$; those are the hypotheses here, and they are exactly the range produced by Lemme 51. $(G_0G_1)^{1/4}$ is two nested `Real.sqrt`.
-- source:
--   P. Dusart, Estimations explicites en Théorie Analytique des Nombres (HDR, 2022), Lemme 55, display (2.43), printed p. 45 (PDF p. 55); definitions (2.7), (2.16), (2.17), (2.19), (2.26), (2.33), (2.34) on printed pp. 38-42; https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf

import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem ExplicitPNT.dusart_G2_lt_exp (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν₀ : (97 / 100 : ℝ) < ν) (hν₁ : ν < 1)
    (hk : X / (2 * Real.pi) *
          Real.sqrt ((ν ^ 2 * (ν - Real.log (2 * Real.pi) / X)) ^ 3 /
            (ν ^ 2 / (2 * ν ^ 2 - 1) *
              (ν + (1 - 2 * Real.log (2 * Real.pi)) / (2 * X)))) *
          Real.exp (-(2 * X * (1 - ν))) * Real.exp (-(X * (1 - ν) ^ 2 / ν)) = 1) :
    let δ := Real.sqrt (2 / Real.pi) *
      Real.sqrt (Real.sqrt
        (ν ^ 6 / (2 * ν ^ 2 - 1) *
          (1 - (Real.log (2 * Real.pi) - 1 / 2) / (X * ν)) *
          (1 - Real.log (2 * Real.pi) / (X * ν)))) *
      Real.exp (-(X * (1 - ν) ^ 2 / ν) / 2) * Real.sqrt X * Real.exp (-X)
    let T₂ := Real.exp (ν * X)
    let q := ((137 / 1000 : ℝ) * Real.log T₂ + 443 / 1000) /
      (T₂ * Real.log T₂ * Real.log (T₂ / (2 * Real.pi)))
    let G₂ := ((1 + δ) ^ 3 + 1) ^ 2 / 2 ^ 2 * (1 + 2 * Real.pi * q)
    G₂ < Real.exp ((264 / 100 : ℝ) * Real.sqrt X * Real.exp (-X)) := by
  sorry
