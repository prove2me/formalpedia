-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_pade_decay_denominator_obstruction
-- name    : EulerMascheroni.Arithmetic.pade_decay_denominator_obstruction
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:03:12.302454+00:00
-- url     : https://prove2.me/theorems/1f7b0603-d958-454a-a531-520d57dbcc52
-- title:
--   Norm–Padé obstruction under the weaker factorial-normalized denominator rate
-- statement:
--   For every real algebraic number $a$, there is no sequence of positive common denominators $D_n$ for $q_0(a),\ldots,q_{2n}(a)$ satisfying
--
--   $$\frac{4^nD_n}{n!}\longrightarrow0.$$
--
--   This strengthens the exponential-denominator obstruction: it needs only the displayed decay rate, not an exponential upper bound.
-- source:
--   Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Lemma 2 and §4.3; Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorem 3.2. Elementary polynomial, differential and norm reductions are derived explicitly here.

import Definitions.Def_eulerMascheroni_padeDecay

theorem EulerMascheroni.Arithmetic.pade_decay_denominator_obstruction (a : ℝ) (ha : IsAlgebraic ℚ a) :
    ¬ EulerMascheroni.Arithmetic.PadeDecayDenominators a := by sorry
