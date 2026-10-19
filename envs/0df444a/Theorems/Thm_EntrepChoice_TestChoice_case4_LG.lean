-- Prove2me | Theorems.Thm_EntrepChoice_TestChoice_case4_LG
-- name    : EntrepChoice.TestChoice.case4_LG
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:19.431021+00:00
-- url     : https://prove2.me/theorems/1eca9338-96a6-446b-8e9a-51bf800b6bf7
-- title:
--   §3.3, p. 11, case 4 — after (L, G) both implementing options are non-positive and abandoning is optimal, V_1(L, G) = 0
-- statement:
--   Assume the standing assumptions and let $(\lambda_v,\lambda_s)\in[0,1]^2$ be a test satisfying (A1). Then:
--
--   1. the signal $(L,G)$ has probability $\Pr(L,G) = p_0(1-e_0)(1-\lambda_v) + (1-p_0)e_0\lambda_s$;
--   2. implementing the tested strategy after $(L,G)$ has (unnormalized) value $-C\,\Pr(L,G)$, which is $\le 0$: if the tested strategy is effective the idea is of low value, so the return is $1\times 0 - C$ or $0\times v - C$;
--   3. the (unnormalized) value of implementing another random strategy is $\Pr(L,G)\,\bigl(e_0p_1(L,G)v - C\bigr)$, which is $\le 0$;
--   4. hence abandoning is optimal and $V_1(L,G) = \max\{e_0p_1(L,G)v - C, 0\} = 0$.
--
--   This is the paper's counter-intuitive case: a signal that the strategy is good, combined with a signal that the idea is poor, leads to abandoning the venture.
--
--   **Formalization Note.** Values are unnormalized (multiplied by $\Pr(L,G)$). The paper's "$e_0p_1(L,G)v - C < 0$" and "both negative" hold only weakly here: under the paper's weak (A1) the switching value may be $0$, and $\Pr(L,G)$ may be $0$ at $\lambda_v = 1, \lambda_s = 0$.
-- source:
--   Agrawal, Gans & Stern, Enabling Entrepreneurial Choice, NBER Working Paper 27379 (June 2020), §3.3, p. 11, case 4

import Mathlib
import Definitions.Def_EntrepChoice_TestChoice_Setting

namespace EntrepChoice.TestChoice
theorem case4_LG (P : Params) (hP : Standing P) (T : Test) (hT : T.Valid) (hA : A1 P T) :
    sigMass P T .LG = P.p0 * (1 - P.e0) * (1 - T.lv) + (1 - P.p0) * P.e0 * T.ls ∧
    actVal P T .LG .implement = -(P.C * sigMass P T .LG) ∧
    actVal P T .LG .implement ≤ 0 ∧
    actVal P T .LG .switch = sigMass P T .LG * (P.e0 * p1 P T .LG * P.v - P.C) ∧
    actVal P T .LG .switch ≤ 0 ∧
    bestVal P T .LG = 0 := by sorry
end EntrepChoice.TestChoice
