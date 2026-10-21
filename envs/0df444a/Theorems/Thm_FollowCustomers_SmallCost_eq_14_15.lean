-- Prove2me | Theorems.Thm_FollowCustomers_SmallCost_eq_14_15
-- name    : FollowCustomers.SmallCost.eq_14_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:47.829582+00:00
-- url     : https://prove2.me/theorems/7449a774-19e1-4a47-871a-d74bda024a49
-- title:
--   (14)–(15), p. 13 (PDF 15) — the threshold system follows from value matching and smooth pasting (5)–(9)
-- statement:
--   Let $r,\sigma^2,\delta>0$, let $K$ be any repositioning cost, and let $A,B,C,\underline x,x^*$ be real numbers such that the value functions
--   $V_d(x)=\pi_d(x)/r+4\delta^2/(9r\lambda^2)+Ae^{\lambda x}+Be^{-\lambda x}$ and $V_s(x)=\pi_s/r+C(e^{\lambda x}+e^{-\lambda x})$ satisfy the value-matching and smooth-pasting conditions (5)–(9). Put $G=e^{\lambda(x^*+\underline x-1)}$. Where the displayed denominators are nonzero, the paper's equations follow:
--   $$G=\frac{\pi_d(x^*)-\pi_s+\pi_d'(x^*)/\lambda+rK+4\delta^2/(9\lambda^2)}{\pi_d(1-\underline x)-\pi_s+\pi_d'(1-\underline x)/\lambda-rK+4\delta^2/(9\lambda^2)},\tag{14}$$
--   $$G=\frac{\pi_d(1-\underline x)-\pi_s-\pi_d'(1-\underline x)/\lambda-rK+4\delta^2/(9\lambda^2)}{\pi_d(x^*)-\pi_s-\pi_d'(x^*)/\lambda+rK+4\delta^2/(9\lambda^2)}.\tag{15}$$
--
--   These equations reduce the five boundary conditions, with three unknown constants, to two equations in the two thresholds alone.
--
--   **Formalization Note.** The two nonzero-denominator hypotheses make the paper's displayed ratios meaningful. Conditions (5)–(9) alone also admit a zero-over-zero case, so the derivation must state these conditions explicitly. In the paper's algebra only (5)–(8) are used; (9) then determines $C$.
-- source:
--   Ning & Villas-Boas, Following the Customers: Dynamic Competitive Repositioning, SSRN 3695318 (December 2020), p. 13 (PDF 15), (14)–(15) from (5)–(9); Appendix pp. 29–30 (PDF 31–32), (i)–(ix)

import Mathlib
import Definitions.Def_FollowCustomers_SmallCost_Model
open Filter Topology

namespace FollowCustomers.SmallCost

/-- The displayed ratio equations (14) and (15) follow from the value-matching and
smooth-pasting conditions (5)–(9), wherever their denominators are nonzero
(p. 13 and Appendix pp. 29–30). -/
theorem eq_14_15 (P : Params) (K xl xs A B C : ℝ) (hP : P.Standing)
    (h : Conditions P K xl xs A B C)
    (hden14 : den14 P K xl ≠ 0) (hden15 : den15 P K xs ≠ 0) :
    Eq14 P K xl xs ∧ Eq15 P K xl xs := by sorry

end FollowCustomers.SmallCost
