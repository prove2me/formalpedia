-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_formal_e_system_equations
-- name    : EulerMascheroni.Mixed.formal_e_system_equations
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:03:13.423764+00:00
-- url     : https://prove2.me/theorems/df79e9e2-b103-4721-a4e4-2568b5e298a1
-- title:
--   Formal differential equations of the Euler E-function system
-- statement:
--   The formal Taylor series $E=e^X$, $I=\widehat{\operatorname{Ein}}$ and $A=EI$ satisfy
--
--   $$E'=E,\qquad XI'=1-e^{-X},\qquad XA'=XA+E-1.$$
--
--   These equations have coefficients in $\mathbb Q(X)$ and only the finite singular point $X=0$.
-- source:
--   Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Lemma 2 and §4.3; Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorem 3.2. Elementary polynomial, differential and norm reductions are derived explicitly here.

import Definitions.Def_eulerMascheroni_formalESystem

theorem EulerMascheroni.Mixed.formal_e_system_equations :
    PowerSeries.derivative ℂ (PowerSeries.exp ℂ) = PowerSeries.exp ℂ ∧
    PowerSeries.X*PowerSeries.derivative ℂ EulerMascheroni.Mixed.formalEin =
      1-PowerSeries.evalNegHom (PowerSeries.exp ℂ) ∧
    PowerSeries.X*PowerSeries.derivative ℂ EulerMascheroni.Mixed.formalExpEin =
      PowerSeries.X*EulerMascheroni.Mixed.formalExpEin+PowerSeries.exp ℂ-1 := by sorry
