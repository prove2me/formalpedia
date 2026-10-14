-- Prove2me | Theorems.Thm_ExplicitPNT_dusart_psi_smoothed_explicit_bound
-- name    : ExplicitPNT.dusart_psi_smoothed_explicit_bound
-- status  : Open
-- author  : @chaikon
-- created : 2026-10-14T03:05:10.746462+00:00
-- url     : https://prove2.me/theorems/c05abeae-ed8c-473b-af68-9f69a305ff11
-- title:
--   Dusart, proof of Théorème 45: $|\psi(x)-x|<xG_2(G_0G_1)^{1/4}\sqrt{8/\pi}X^{1/2}e^{-X}(1+3.27X^{1/2}e^{-X})$
-- statement:
--   Let $R>0$ be such that $\zeta(s)\neq0$ whenever $|\Im s|>2\pi$ and $\Re s>1-\frac{1}{R\log|\Im s|}$. For $x>0$ put $X=\sqrt{\log x/R}$ and assume $X>\max(8.36,8/R)$. Let $0.97<\nu<1$ satisfy $k(\nu)=1$, and let $Y$, $T_2=e^{\nu X}$, $\delta$, $q$, $G_2$ and $G_0G_1$ be as in `ExplicitPNT.dusart_G2_lt_exp` (Dusart's (2.17), (2.19), (2.34), (2.16), (2.26) and Lemme 52 with $m=2$). Then
--   $$|\psi(x)-x|<x\,G_2\,(G_0G_1)^{1/4}\sqrt{\frac8\pi}\,X^{1/2}e^{-X}\bigl(1+3.27\,X^{1/2}e^{-X}\bigr).$$
--
--   This is the analytic core of the proof of Dusart's Théorème 45 (printed p. 46): the display just before the last appeal to Lemme 55. It is obtained by: Lemma 8 of Rosser–Schoenfeld (1975) with $m=2$, i.e. (2.12),
--   $$\frac1x|\psi(x)-x|<\frac{S_1(2,\delta)+S_2(2,\delta)}{\sqrt x}+S_3(2,\delta)+S_4(2,\delta)+\delta+\frac{\log 2\pi}{x};$$
--   Lemme 50 (with the zero-free region, the zero-counting bounds (2.2), and RH verified up to $T_0=17.8478\ldots$) giving $S_3+S_4+\delta<G_2(G_0G_1)^{1/4}\sqrt{8/\pi}X^{1/2}e^{-X}+4G_2R(T_2)\varphi_0(T_2)$; Lemme 53 ($R(T_2)\varphi_0(T_2)<1.15Xe^{-2X}$) and Lemme 52 ($G_0G_1>0.61$), turning the last term into $3.2618\,X^{1/2}e^{-X}$ times the main term; and Lemme 54, which bounds $(S_1+S_2)/\sqrt x+\log(2\pi)/x$ (and the $1.43/\sqrt x$ needed for $\vartheta$) by $0.0033$ times $G_2(G_0G_1)^{1/4}\sqrt{8/\pi}Xe^{-2X}$, using $X>8/R$.
--
--   **Formalization note.** The smoothing parameter enters through the explicit equation $k(\nu)=1$ (written out as in `ExplicitPNT.dusart_k_root_exists`), which by Lemme 51 has a unique solution in $(0.97,1)$; this makes $T_2=e^{\nu X}$ (2.19) agree with the optimised choice (2.33). Fourth roots are two nested `Real.sqrt`.
-- source:
--   P. Dusart, Estimations explicites en Théorie Analytique des Nombres (HDR, 2022), proof of Théorème 45, printed p. 46 (PDF p. 56), first four displays, using (2.12) (= Rosser-Schoenfeld, Math. Comp. 29 (1975), Lemma 8) and Lemmes 50, 52, 53, 54 on printed pp. 42-45; https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf . Restates the proof of Theorem 1.1 of Dusart, Math. Comp. 85 (2016), 875-888.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem ExplicitPNT.dusart_psi_smoothed_explicit_bound
    (R : ℝ) (hR : 0 < R)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (x : ℝ) (hx : 0 < x)
    (hX : max (836 / 100 : ℝ) (8 / R) < Real.sqrt (Real.log x / R)) :
    let X := Real.sqrt (Real.log x / R)
    ∀ ν : ℝ, (97 / 100 : ℝ) < ν → ν < 1 →
      X / (2 * Real.pi) *
          Real.sqrt ((ν ^ 2 * (ν - Real.log (2 * Real.pi) / X)) ^ 3 /
            (ν ^ 2 / (2 * ν ^ 2 - 1) *
              (ν + (1 - 2 * Real.log (2 * Real.pi)) / (2 * X)))) *
          Real.exp (-(2 * X * (1 - ν))) * Real.exp (-(X * (1 - ν) ^ 2 / ν)) = 1 →
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
      |Chebyshev.psi x - x| <
        x * G₂ *
          Real.sqrt (Real.sqrt
            (ν ^ 6 / (2 * ν ^ 2 - 1) *
              (1 - (Real.log (2 * Real.pi) - 1 / 2) / (X * ν)) *
              (1 - Real.log (2 * Real.pi) / (X * ν)))) *
          Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) *
          (1 + (327 / 100 : ℝ) * Real.sqrt X * Real.exp (-X)) := by
  sorry
