-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_rCoef_isInt
-- name    : EulerMascheroni.Rivoal.rCoef_isInt
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:13:13.985714+00:00
-- url     : https://prove2.me/theorems/089e6183-7121-4ed8-9255-041fdb8e460f
-- title:
--   $r'_n$ is an integer
-- statement:
--   For every $n\ge0$,
--   $$
--   r'_n=\sum_{j=0}^n\frac{(3n-j)!}{\big(j!\,(n-j)!\big)^2}\in\mathbb Z .
--   $$
--   Here $\beta_{n,j},h_{n,j},p'_n,q'_n,r'_n,S_n,d(3n)$ are the data of the definition `eulerMascheroni_rivoalForms`.
--
--   Each summand is an integer: it equals a multinomial coefficient times $n!/j!$. This is part of the integrality of Rivoal's forms.
-- source:
--   T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 (eq. 3.5) and Lemma 4, at z=-1 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); finite-sum form and elementary proof: Lemma B1 of the accompanying research notes (Beta-integral series, partial fractions, alternating-series bounds).

import Definitions.Def_eulerMascheroni_rivoalForms

theorem EulerMascheroni.Rivoal.rCoef_isInt (n : ℕ) :
    ∃ z : ℤ, EulerMascheroni.Rivoal.rCoef n = z := by sorry
