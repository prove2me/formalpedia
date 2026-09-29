-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_formal_expEin_harmonic_coefficients
-- name    : EulerMascheroni.Mixed.formal_expEin_harmonic_coefficients
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:14:51.949311+00:00
-- url     : https://prove2.me/theorems/22a89b47-78a5-4aa9-85c2-b6f229378436
-- title:
--   Harmonic numbers are the factorial-normalized coefficients of exp times Ein
-- statement:
--   The formal series $A=e^X\operatorname{Ein}(X)$ has coefficients
--
--   $$A(X)=\sum_{n\ge0}\frac{H_n}{n!}X^n,\qquad H_n=\sum_{j=1}^n\frac1j.$$
--
--   In particular its factorial-normalized coefficients are rational harmonic numbers. This identifies the arithmetic coefficients relevant to its E-function structure.
-- source:
--   Explicit consequences of the Euler E-system and factorial-quotient recurrence, derived for this decomposition. Compare Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorems 2.5 and 3.2, and Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, §4.1 and §4.3.

import Definitions.Def_eulerMascheroni_formalESystem

theorem EulerMascheroni.Mixed.formal_expEin_harmonic_coefficients (n : ℕ) :
    (n.factorial:ℂ)*PowerSeries.coeff n EulerMascheroni.Mixed.formalExpEin = (harmonic n:ℂ) := by sorry
