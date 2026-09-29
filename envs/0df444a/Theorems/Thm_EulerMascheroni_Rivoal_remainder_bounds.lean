-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_remainder_bounds
-- name    : EulerMascheroni.Rivoal.remainder_bounds
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:13:27.488503+00:00
-- url     : https://prove2.me/theorems/5688b1b0-2973-4382-ae44-42dab14b1a9e
-- title:
--   Positivity and size of the remainder $S_n$
-- statement:
--   For every $n\ge0$,
--   $$
--   0<S_n\le\frac{1}{\big((n+1)!\big)^2},\qquad S_n=\sum_{m\ge0}\frac{(-1)^m}{m!}\left(\frac{(m+2n)!}{(m+3n+1)!}\right)^2 .
--   $$
--   Here $\beta_{n,j},h_{n,j},p'_n,q'_n,r'_n,S_n,d(3n)$ are the data of the definition `eulerMascheroni_rivoalForms`.
--
--   The series is alternating and its terms strictly decrease, so $S_n$ lies strictly between $0$ and its first term $\big((2n)!/(3n+1)!\big)^2\le 1/((n+1)!)^2$. This gives both the non-vanishing and the decay of Rivoal's linear forms.
-- source:
--   T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 (eq. 3.5) and Lemma 4, at z=-1 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); finite-sum form and elementary proof: Lemma F2 of the accompanying research notes (Beta-integral series, partial fractions, alternating-series bounds).

import Definitions.Def_eulerMascheroni_rivoalForms

theorem EulerMascheroni.Rivoal.remainder_bounds (n : ℕ) :
    0 < EulerMascheroni.Rivoal.remainder n ∧
      EulerMascheroni.Rivoal.remainder n ≤ 1 / ((n + 1).factorial : ℝ) ^ 2 := by sorry
