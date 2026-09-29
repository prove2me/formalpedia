-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_den_mul_qCoef_isInt
-- name    : EulerMascheroni.Rivoal.den_mul_qCoef_isInt
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:13:16.557459+00:00
-- url     : https://prove2.me/theorems/484fcdc7-6a55-4706-8af3-525ae3c882e5
-- title:
--   $d(3n)\,q'_n$ is an integer
-- statement:
--   For every $n\ge0$, with $d(3n)=\operatorname{lcm}(1,\dots,3n)$,
--   $$
--   d(3n)\,q'_n=-\,d(3n)\sum_{j=0}^n\beta_{n,j}\big(H_{3n-j}+2H_j-2H_{n-j}\big)\in\mathbb Z .
--   $$
--   Here $\beta_{n,j},h_{n,j},p'_n,q'_n,r'_n,S_n,d(3n)$ are the data of the definition `eulerMascheroni_rivoalForms`.
--
--   The coefficient of $e$ in Rivoal's forms has only harmonic-number denominators, which $d(3n)$ clears.
-- source:
--   T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 (eq. 3.5) and Lemma 4, at z=-1 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); finite-sum form and elementary proof: Lemma F0-int of the accompanying research notes (Beta-integral series, partial fractions, alternating-series bounds).

import Definitions.Def_eulerMascheroni_rivoalForms

theorem EulerMascheroni.Rivoal.den_mul_qCoef_isInt (n : ℕ) :
    ∃ z : ℤ, (EulerMascheroni.Rivoal.den n : ℚ) * EulerMascheroni.Rivoal.qCoef n = z := by sorry
