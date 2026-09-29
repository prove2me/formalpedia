-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_pCoef_isInt
-- name    : EulerMascheroni.Rivoal.pCoef_isInt
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:13:12.167645+00:00
-- url     : https://prove2.me/theorems/517435db-118a-45dd-ae70-bf3cf893b8ae
-- title:
--   $p'_n$ is an integer
-- statement:
--   For every $n\ge1$ the constant coefficient $p'_n$ of Rivoal's form is a rational integer:
--   $$
--   p'_n=\sum_{i=0}^{n-1}E_{n-1-i}\Big(\beta_{n,i}h_{n,i}+\sum_{k<i}\frac{(-1)^{i-k}\beta_{n,k}}{(i-k)(i-k)!}\Big)\in\mathbb Z .
--   $$
--   Here $\beta_{n,j},h_{n,j},p'_n,q'_n,r'_n,S_n,d(3n)$ are the data of the definition `eulerMascheroni_rivoalForms`.
--
--   This is one of the integrality statements needed to turn the forms into integer linear forms. The summands have large denominators, and the claim is that they cancel.
-- source:
--   T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 (eq. 3.5) and Lemma 4, at z=-1 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); finite-sum form and elementary proof: Lemma F0-int (via A1, A5) of the accompanying research notes (Beta-integral series, partial fractions, alternating-series bounds).

import Definitions.Def_eulerMascheroni_rivoalForms

theorem EulerMascheroni.Rivoal.pCoef_isInt (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, EulerMascheroni.Rivoal.pCoef n = z := by sorry
