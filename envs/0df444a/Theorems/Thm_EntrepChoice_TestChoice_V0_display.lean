-- Prove2me | Theorems.Thm_EntrepChoice_TestChoice_V0_display
-- name    : EntrepChoice.TestChoice.V0_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:18.926428+00:00
-- url     : https://prove2.me/theorems/b9e384b7-a7e9-43c8-95b9-0e160baea456
-- title:
--   §3.3, p. 12, V_0 display (first line) — V_0(λ_v, λ_s) = p_0e_0(v − C) + (p_0(1 − e_0)λ_v + (1 − p_0)e_0(1 − λ_s))V_1(H, B) − c
-- statement:
--   Assume the standing assumptions and let $(\lambda_v,\lambda_s)\in[0,1]^2$ be any test satisfying (A1). Then the value of testing, computed with optimal period-1 actions after each of the four signals, equals
--   $$V_0(\lambda_v,\lambda_s) = p_0e_0(v-C) + \bigl(p_0(1-e_0)\lambda_v + (1-p_0)e_0(1-\lambda_s)\bigr)\bigl(e_0p_1(H,B)v - C\bigr) - c ,$$
--   where $e_0p_1(H,B)v - C = V_1(H,B)$ is the value after an $(H,B)$ signal (case 3) and $V_1(L,G) = V_1(L,B) = 0$.
--
--   This closed form is what Proposition 2 compares at the two precise tests $(\lambda_v,1)$ and $(1,\lambda_s)$.
--
--   **Formalization Note.** Only the first line of the paper's display is stated. The printed second line, $p_0e_0(1+(1-e_0)\lambda_v)(v-C) - (1-p_0)e_0(1-\lambda_s)C - c$, differs from the first by $p_0(1-e_0)^2\lambda_vC$ and is not a valid identity. The statement covers every valid test with (A1), including the precise tests with $\lambda_v = 1$ or $\lambda_s = 1$.
-- source:
--   Agrawal, Gans & Stern, Enabling Entrepreneurial Choice, NBER Working Paper 27379 (June 2020), §3.3, p. 12, V_0(λ_v, λ_s) display, first line

import Mathlib
import Definitions.Def_EntrepChoice_TestChoice_Setting

namespace EntrepChoice.TestChoice
theorem V0_display (P : Params) (hP : Standing P) (T : Test) (hT : T.Valid) (hA : A1 P T) :
    testValue P T = P.p0 * P.e0 * (P.v - P.C)
      + (P.p0 * (1 - P.e0) * T.lv + (1 - P.p0) * P.e0 * (1 - T.ls))
        * (P.e0 * p1 P T .HB * P.v - P.C) - P.c := by sorry
end EntrepChoice.TestChoice
