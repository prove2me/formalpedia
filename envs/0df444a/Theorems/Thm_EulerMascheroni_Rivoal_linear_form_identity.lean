-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_linear_form_identity
-- name    : EulerMascheroni.Rivoal.linear_form_identity
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:13:31.569489+00:00
-- url     : https://prove2.me/theorems/2aa4513a-eff0-4dcc-acb8-1f6efb44283a
-- title:
--   Linear form identity for Rivoal's forms
-- statement:
--   For every $n\ge1$,
--   $$
--   p'_n+q'_n\,e+r'_n\,\theta=e\,S_n,\qquad \theta=e\operatorname{Ein}(1),\quad S_n=\sum_{m\ge0}\frac{(-1)^m}{m!}\left(\frac{(m+2n)!}{(m+3n+1)!}\right)^2 .
--   $$
--   Here $\beta_{n,j},h_{n,j},p'_n,q'_n,r'_n,S_n,d(3n)$ are the data of the definition `eulerMascheroni_rivoalForms`.
--
--   This identity shows that the explicit rational triple $(p'_n,q'_n,r'_n)$ gives a linear form in $1,e,\theta$ whose value is the rapidly decaying alternating series $eS_n$. It is the analytic core of the elementary proof that $1,e,\theta$ are $\mathbb Q$-linearly independent.
--
--   **Formalization Note** The identity is stated in $\mathbb C$, with $\theta$ given by the platform function `EulerMascheroni.Mixed.expEin 1` $=e\operatorname{Ein}(1)$.
-- source:
--   T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 (eq. 3.5) and Lemma 4, at z=-1 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); finite-sum form and elementary proof: Lemma F1 of the accompanying research notes (Beta-integral series, partial fractions, alternating-series bounds).

import Definitions.Def_eulerMascheroni_rivoalForms
import Definitions.Def_eulerMascheroni_mixedCover

theorem EulerMascheroni.Rivoal.linear_form_identity (n : ℕ) (hn : 1 ≤ n) :
    ((EulerMascheroni.Rivoal.pCoef n : ℚ) : ℂ)
      + ((EulerMascheroni.Rivoal.qCoef n : ℚ) : ℂ) * Complex.exp 1
      + ((EulerMascheroni.Rivoal.rCoef n : ℚ) : ℂ) * EulerMascheroni.Mixed.expEin 1
      = Complex.exp 1 * ((EulerMascheroni.Rivoal.remainder n : ℝ) : ℂ) := by sorry
