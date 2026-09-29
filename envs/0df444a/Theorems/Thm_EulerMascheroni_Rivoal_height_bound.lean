-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_height_bound
-- name    : EulerMascheroni.Rivoal.height_bound
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:13:19.265726+00:00
-- url     : https://prove2.me/theorems/37d8d807-9f3c-4970-bffa-11508486fea7
-- title:
--   Height bound for Rivoal's forms
-- statement:
--   For every $n\ge0$,
--   $$
--   |q'_n|+|r'_n|\le(9n+1)\,108^n\,n! .
--   $$
--   Here $\beta_{n,j},h_{n,j},p'_n,q'_n,r'_n,S_n,d(3n)$ are the data of the definition `eulerMascheroni_rivoalForms`.
--
--   This bound controls the size of the coefficients of $e$ and $\theta$ in Rivoal's forms. It grows like $C^n n!$, whereas the forms decay like $C^n/(n!)^2$.
-- source:
--   T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 (eq. 3.5) and Lemma 4, at z=-1 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); finite-sum form and elementary proof: Lemma F3 of the accompanying research notes (Beta-integral series, partial fractions, alternating-series bounds).

import Definitions.Def_eulerMascheroni_rivoalForms

theorem EulerMascheroni.Rivoal.height_bound (n : ℕ) :
    |EulerMascheroni.Rivoal.qCoef n| + |EulerMascheroni.Rivoal.rCoef n|
      ≤ (9 * n + 1) * 108 ^ n * (n.factorial : ℚ) := by sorry
