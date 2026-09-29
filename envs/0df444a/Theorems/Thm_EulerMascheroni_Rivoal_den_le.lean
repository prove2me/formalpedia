-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_den_le
-- name    : EulerMascheroni.Rivoal.den_le
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:13:15.745009+00:00
-- url     : https://prove2.me/theorems/54c7f46e-795d-4b03-b605-7bcb3033f20d
-- title:
--   $\operatorname{lcm}(1,\dots,3n)\le 11^{3n}$
-- statement:
--   For every $n\ge0$,
--   $$
--   d(3n)=\operatorname{lcm}(1,2,\dots,3n)\le 11^{3n}.
--   $$
--   Here $\beta_{n,j},h_{n,j},p'_n,q'_n,r'_n,S_n,d(3n)$ are the data of the definition `eulerMascheroni_rivoalForms`.
--
--   This is a crude Chebyshev-type bound; any exponential bound suffices for the application. It follows from $\operatorname{lcm}(1,\dots,m)\le 4^m m^{\lfloor\sqrt m\rfloor}\le(4e)^m$, using the primorial bound $\prod_{p\le m}p\le4^m$.
-- source:
--   T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 (eq. 3.5) and Lemma 4, at z=-1 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); finite-sum form and elementary proof: Lemma F4a of the accompanying research notes (Beta-integral series, partial fractions, alternating-series bounds).

import Definitions.Def_eulerMascheroni_rivoalForms

theorem EulerMascheroni.Rivoal.den_le (n : ℕ) :
    (EulerMascheroni.Rivoal.den n : ℝ) ≤ 11 ^ (3 * n) := by sorry
