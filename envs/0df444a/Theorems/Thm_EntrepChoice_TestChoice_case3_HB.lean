-- Prove2me | Theorems.Thm_EntrepChoice_TestChoice_case3_HB
-- name    : EntrepChoice.TestChoice.case3_HB
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:23.783151+00:00
-- url     : https://prove2.me/theorems/c64f53b0-9e58-4482-a7b6-5e4ebb5b2e77
-- title:
--   §3.3, p. 11, case 3 — after (H, B) switching to another random strategy is optimal, with value Pr(H, B)(e_0p_1(H, B)v − C) ≥ 0
-- statement:
--   Assume the standing assumptions and let $(\lambda_v,\lambda_s)\in[0,1]^2$ be a test satisfying (A1). Then:
--
--   1. the signal $(H,B)$ has probability $\Pr(H,B) = p_0(1-e_0)\lambda_v + (1-p_0)e_0(1-\lambda_s)$;
--   2. implementing another random strategy is at least as good as implementing the tested one after $(H,B)$, and strictly better when $\lambda_v>0$;
--   3. the (unnormalized) value of switching is $\Pr(H,B)\,\bigl(e_0p_1(H,B)v - C\bigr)$;
--   4. switching is at least as good as abandoning;
--   5. hence switching is optimal: $\Pr(H,B)\,V_1(H,B) = \Pr(H,B)\,\bigl(e_0p_1(H,B)v - C\bigr)$, i.e. $V_1(H,B) = \max\{e_0p_1(H,B)v - C, 0\} = e_0p_1(H,B)v - C$.
--
--   This is the paper's case 3: an $(H,B)$ signal raises the belief in the idea and lowers the belief in the tested strategy, so the entrepreneur switches strategies.
--
--   **Formalization Note.** Values are unnormalized (multiplied by $\Pr(H,B)$). The paper's "$e_0p_1(H,B)v - C > 0$" holds only weakly under the paper's weak (A1) (equality when $p_1(H,B) = p_0$), so items 4–5 are weak.
-- source:
--   Agrawal, Gans & Stern, Enabling Entrepreneurial Choice, NBER Working Paper 27379 (June 2020), §3.3, p. 11, case 3

import Mathlib
import Definitions.Def_EntrepChoice_TestChoice_Setting

namespace EntrepChoice.TestChoice
theorem case3_HB (P : Params) (hP : Standing P) (T : Test) (hT : T.Valid) (hA : A1 P T) :
    sigMass P T .HB = P.p0 * (1 - P.e0) * T.lv + (1 - P.p0) * P.e0 * (1 - T.ls) ∧
    actVal P T .HB .implement ≤ actVal P T .HB .switch ∧
    (0 < T.lv → actVal P T .HB .implement < actVal P T .HB .switch) ∧
    actVal P T .HB .switch = sigMass P T .HB * (P.e0 * p1 P T .HB * P.v - P.C) ∧
    actVal P T .HB .abandon ≤ actVal P T .HB .switch ∧
    bestVal P T .HB = actVal P T .HB .switch := by sorry
end EntrepChoice.TestChoice
