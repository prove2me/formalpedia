-- Prove2me | Theorems.Thm_FixedPointAA_Main_reflections_matrix_form
-- name    : FixedPointAA.Main.reflections_matrix_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:03.218508+00:00
-- url     : https://prove2.me/theorems/c4abd328-ca14-4e24-a1b2-caa22fb67595
-- title:
--   Eqs. (6)–(7), p. 2 — generalized reflections in two coordinates
-- statement:
--   For $0\le\lambda\le1$, write $\bar\lambda=1-\lambda$ and $|s\rangle=(\sqrt{\bar\lambda},\sqrt\lambda)$. For real phases $\alpha,\beta$, the two generalized reflections are
--
--   $$S_s(\alpha)=\begin{pmatrix}1-(1-e^{-i\alpha})\bar\lambda&-(1-e^{-i\alpha})\sqrt{\lambda\bar\lambda}\\-(1-e^{-i\alpha})\sqrt{\lambda\bar\lambda}&1-(1-e^{-i\alpha})\lambda\end{pmatrix},\quad S_t(\beta)=\begin{pmatrix}1&0\\0&e^{i\beta}\end{pmatrix}.$$
--
--   These formulas pin down the phase signs and coordinate order for the rotation identities.
-- source:
--   Yoder, Low, Chuang, Fixed-point quantum search with an optimal number of queries, arXiv:1409.3305v2, p. 2, Eqs. (6)–(7)

import Mathlib
import Definitions.Def_FixedPointAA_Main_Setting

namespace FixedPointAA.Main
open scoped Matrix

/-- Eqs. (6)–(7) in the basis of Eq. (4). -/
theorem reflections_matrix_form (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (α β : ℝ) :
    Ss (sVec lam) α =
      !![1 - (1 - Complex.exp (-(α : ℂ) * Complex.I)) * ((1 - lam : ℝ) : ℂ),
          -(1 - Complex.exp (-(α : ℂ) * Complex.I)) * ((Real.sqrt (lam * (1 - lam)) : ℝ) : ℂ);
          -(1 - Complex.exp (-(α : ℂ) * Complex.I)) * ((Real.sqrt (lam * (1 - lam)) : ℝ) : ℂ),
          1 - (1 - Complex.exp (-(α : ℂ) * Complex.I)) * (lam : ℂ)] ∧
    St tVec β = !![1, 0; 0, Complex.exp ((β : ℂ) * Complex.I)] := by sorry

end FixedPointAA.Main
