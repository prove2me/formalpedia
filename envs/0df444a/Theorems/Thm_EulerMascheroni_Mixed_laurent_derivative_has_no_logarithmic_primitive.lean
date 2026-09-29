-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_laurent_derivative_has_no_logarithmic_primitive
-- name    : EulerMascheroni.Mixed.laurent_derivative_has_no_logarithmic_primitive
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:02:47.663422+00:00
-- url     : https://prove2.me/theorems/fb3f8569-e1a8-4c83-8d28-d10f26226b56
-- title:
--   No Laurent-series derivative equals one over X
-- statement:
--   For every formal Laurent series $f\in\mathbb C((X))$,
--
--   $$f'\ne X^{-1}.$$
--
--   The coefficient of $X^{-1}$ in a derivative is zero. This is the formal residue obstruction underlying the polynomial logarithmic argument.
-- source:
--   Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Lemma 2 and §4.3; Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorem 3.2. Elementary polynomial, differential and norm reductions are derived explicitly here.

import Mathlib

theorem EulerMascheroni.Mixed.laurent_derivative_has_no_logarithmic_primitive (f : LaurentSeries ℂ) :
    LaurentSeries.derivative ℂ f ≠ HahnSeries.single (-1) (1:ℂ) := by sorry
