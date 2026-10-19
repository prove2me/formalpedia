-- Prove2me | Theorems.Thm_EntrepChoice_TestChoice_proposition_1
-- name    : EntrepChoice.TestChoice.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:17.231072+00:00
-- url     : https://prove2.me/theorems/d45d8ad5-0e6c-404e-a977-787a8d23de24
-- title:
--   Proposition 1, p. 12 — only an (H, G) signal leads to implementing the tested strategy; (L, B), and (L, G) under V_0 = 0, lead to abandonment
-- statement:
--   Assume the standing assumptions (in particular $V_0 = e_0p_0v - C = 0$) and let $(\lambda_v,\lambda_s)$ be a baseline test, $0<\lambda_v<1$ and $0<\lambda_s<1$, satisfying (A1). Compare the three period-1 actions (implement the tested strategy, implement another random strategy, abandon) after each signal:
--
--   1. after $(H,G)$, implementing the tested strategy is strictly better than both alternatives;
--   2. after every other signal, implementing the tested strategy is strictly worse than the best action — so the tested strategy is implemented only after $(H,G)$;
--   3. after $(H,B)$ and after $(L,G)$, implementing another random strategy is strictly better than implementing the tested strategy;
--   4. after $(L,B)$, abandoning is strictly better than both implementing options;
--   5. after $(L,G)$, abandoning is at least as good as both implementing options.
--
--   In short, only a clear positive signal leads to implementation of the tested strategy, and an $(L,G)$ signal leads to abandonment when $V_0 = 0$.
--
--   **Formalization Note.** The paper's second sentence lacks its verb; it is read as "selecting another strategy at random to implement is strictly better than implementing the tested strategy". "Implemented"/"abandoned" are read as "attains the optimum"; item 5 is weak because the paper's (A1) is weak. The baseline range $0<\lambda_v,\lambda_s<1$ follows p. 7 (the posteriors are strictly below $1$); at $\lambda_v = 1$ the $(L,G)$ comparison in item 3 is a tie.
-- source:
--   Agrawal, Gans & Stern, Enabling Entrepreneurial Choice, NBER Working Paper 27379 (June 2020), Proposition 1, p. 12

import Mathlib
import Definitions.Def_EntrepChoice_TestChoice_Setting

namespace EntrepChoice.TestChoice
theorem proposition_1 (P : Params) (hP : Standing P) (T : Test)
    (hlv : 0 < T.lv ∧ T.lv < 1) (hls : 0 < T.ls ∧ T.ls < 1) (hA : A1 P T) :
    -- (H, G): the tested strategy is implemented
    (actVal P T .HG .switch < actVal P T .HG .implement ∧
      actVal P T .HG .abandon < actVal P T .HG .implement) ∧
    -- only after (H, G): after every other signal implementing is strictly suboptimal
    (∀ σ : Sig, σ ≠ .HG → actVal P T σ .implement < bestVal P T σ) ∧
    -- (H, B) and (L, G): another random strategy is strictly better than the tested one
    actVal P T .HB .implement < actVal P T .HB .switch ∧
    actVal P T .LG .implement < actVal P T .LG .switch ∧
    -- (i) (L, B): the venture is abandoned
    (actVal P T .LB .implement < actVal P T .LB .abandon ∧
      actVal P T .LB .switch < actVal P T .LB .abandon) ∧
    -- (ii) (L, G) under V₀ = 0: the venture is abandoned
    (actVal P T .LG .implement ≤ actVal P T .LG .abandon ∧
      actVal P T .LG .switch ≤ actVal P T .LG .abandon) := by sorry
end EntrepChoice.TestChoice
