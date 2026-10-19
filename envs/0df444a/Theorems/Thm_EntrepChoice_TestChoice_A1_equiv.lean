-- Prove2me | Theorems.Thm_EntrepChoice_TestChoice_A1_equiv
-- name    : EntrepChoice.TestChoice.A1_equiv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:16.464231+00:00
-- url     : https://prove2.me/theorems/6aa09a9a-a5e4-4d87-8c36-6061bbe2eee8
-- title:
--   (A1), p. 9 — for a test with 0 < λ_v, λ_s < 1, each posterior clause of (A1) is equivalent to its ratio form
-- statement:
--   Assume the standing assumptions $0<p_0<1$, $0<e_0<1$, $v>0$, $e_0p_0v = C$, $c<C$, and let $0<\lambda_v<1$, $0<\lambda_s<1$. Then (A1) in its cross-multiplied form is equivalent to the four posterior inequalities $p_1(H,B)\ge p_0$, $p_1(L,G)\le p_0$, $e_1(H,B)\le e_0$, $e_1(L,G)\ge e_0$, and each of these is equivalent to the ratio condition the paper gives in parentheses:
--   $$p_1(H,B)\ge p_0 \iff \frac{\lambda_v}{1-\lambda_s}\ge\frac{e_0}{1-e_0},\qquad p_1(L,G)\le p_0 \iff \frac{1-\lambda_v}{\lambda_s}\le\frac{e_0}{1-e_0},$$
--   $$e_1(H,B)\le e_0 \iff \frac{1-\lambda_s}{\lambda_v}\le\frac{p_0}{1-p_0},\qquad e_1(L,G)\ge e_0 \iff \frac{\lambda_s}{1-\lambda_v}\ge\frac{p_0}{1-p_0} .$$
--
--   The result translates the informativeness assumption on posteriors into explicit lower bounds on the precisions $(\lambda_v,\lambda_s)$.
--
--   **Formalization Note.** The paper prints the second ratio condition with a strict "$<$"; the posterior condition $p_1(L,G)\le p_0$ is equivalent to the weak inequality, which is what is stated. The range $0<\lambda_v,\lambda_s<1$ is the baseline test of p. 7, where all four ratios have positive denominators.
-- source:
--   Agrawal, Gans & Stern, Enabling Entrepreneurial Choice, NBER Working Paper 27379 (June 2020), (A1), p. 9

import Mathlib
import Definitions.Def_EntrepChoice_TestChoice_Setting

namespace EntrepChoice.TestChoice
theorem A1_equiv (P : Params) (hP : Standing P) (T : Test)
    (hlv : 0 < T.lv ∧ T.lv < 1) (hls : 0 < T.ls ∧ T.ls < 1) :
    (A1 P T ↔ (P.p0 ≤ p1 P T .HB ∧ p1 P T .LG ≤ P.p0 ∧
                e1 P T .HB ≤ P.e0 ∧ P.e0 ≤ e1 P T .LG)) ∧
    (P.p0 ≤ p1 P T .HB ↔ P.e0 / (1 - P.e0) ≤ T.lv / (1 - T.ls)) ∧
    (p1 P T .LG ≤ P.p0 ↔ (1 - T.lv) / T.ls ≤ P.e0 / (1 - P.e0)) ∧
    (e1 P T .HB ≤ P.e0 ↔ (1 - T.ls) / T.lv ≤ P.p0 / (1 - P.p0)) ∧
    (P.e0 ≤ e1 P T .LG ↔ P.p0 / (1 - P.p0) ≤ T.ls / (1 - T.lv)) := by sorry
end EntrepChoice.TestChoice
