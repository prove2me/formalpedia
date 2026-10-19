-- Prove2me | Theorems.Thm_EntrepChoice_TestChoice_posteriors
-- name    : EntrepChoice.TestChoice.posteriors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:25.130439+00:00
-- url     : https://prove2.me/theorems/7b94fffa-1b06-4344-8f65-c5ad79cd3573
-- title:
--   §3.1, p. 9, Bayes-law display — the posteriors p_1(H, B), p_1(L, G), e_1(H, B), e_1(L, G) of a test (λ_v, λ_s)
-- statement:
--   Fix parameters $p_0, e_0$ and a test with precisions $(\lambda_v,\lambda_s)$. The Bayes posteriors after the two conflated signals are
--   $$p_1(H,B) = \frac{p_0(1-e_0)\lambda_v}{(1-p_0)e_0(1-\lambda_s)+p_0(1-e_0)\lambda_v},\qquad p_1(L,G) = \frac{p_0(1-e_0)(1-\lambda_v)}{(1-p_0)e_0\lambda_s+p_0(1-e_0)(1-\lambda_v)},$$
--   $$e_1(H,B) = \frac{(1-p_0)e_0(1-\lambda_s)}{(1-p_0)e_0(1-\lambda_s)+p_0(1-e_0)\lambda_v},\qquad e_1(L,G) = \frac{(1-p_0)e_0\lambda_s}{(1-p_0)e_0\lambda_s+p_0(1-e_0)(1-\lambda_v)} .$$
--
--   Here $p_1(\sigma)$ is the posterior probability that the idea has high value and $e_1(\sigma)$ the posterior probability that the tested strategy is effective. The identities pin the signal table of the model to the paper's printed posteriors.
--
--   **Formalization Note.** The identities are stated for all real parameters; when a denominator vanishes both sides are $0$ under Lean's convention $x/0 = 0$.
-- source:
--   Agrawal, Gans & Stern, Enabling Entrepreneurial Choice, NBER Working Paper 27379 (June 2020), §3.1, p. 9, Bayes-law display

import Mathlib
import Definitions.Def_EntrepChoice_TestChoice_Setting

namespace EntrepChoice.TestChoice
theorem posteriors (P : Params) (T : Test) :
    p1 P T .HB = P.p0 * (1 - P.e0) * T.lv
        / ((1 - P.p0) * P.e0 * (1 - T.ls) + P.p0 * (1 - P.e0) * T.lv) ∧
    p1 P T .LG = P.p0 * (1 - P.e0) * (1 - T.lv)
        / ((1 - P.p0) * P.e0 * T.ls + P.p0 * (1 - P.e0) * (1 - T.lv)) ∧
    e1 P T .HB = (1 - P.p0) * P.e0 * (1 - T.ls)
        / ((1 - P.p0) * P.e0 * (1 - T.ls) + P.p0 * (1 - P.e0) * T.lv) ∧
    e1 P T .LG = (1 - P.p0) * P.e0 * T.ls
        / ((1 - P.p0) * P.e0 * T.ls + P.p0 * (1 - P.e0) * (1 - T.lv)) := by sorry
end EntrepChoice.TestChoice
