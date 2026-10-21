-- Prove2me | Theorems.Thm_BuyXFree_Threshold_case_a_d_bounds
-- name    : BuyXFree.Threshold.case_a_d_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:53.676157+00:00
-- url     : https://prove2.me/theorems/0f044c32-bdd5-4b57-8222-84c559c35d7a
-- title:
--   §4.1, pp. 11–12 — π*_a ≤ λ(v − v̄) and π*_d ≤ λqv
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. Suppose $k=0$. In case (a) the stationary demand is $\lambda X/(X+1)$ and the admissible prices are $p\le p^D(0)$; in case (d) the demand is $\lambda qX/(X+1)$ and the admissible prices are $p\le\frac{(1-A^{X+1})v}{1-A^X}$ (proof of Lemma 10, p. 48). Then
--   $$p\le p^D(0)\ \Longrightarrow\ \frac{\lambda X}{X+1}\,p\le\lambda(v-\bar v),\qquad p\le\frac{(1-A^{X+1})v+A^X(1-A)k}{1-A^X}\ \Longrightarrow\ \frac{\lambda qX}{X+1}\,p\le\lambda qv .$$
--
--   Hence $\pi^*_a\le\lambda(v-\bar v)$ and $\pi^*_d\le\lambda qv$: cases (a) and (d) cannot beat the no-program profit.
--
--   **Formalization Note** The profits $\pi^*_a$, $\pi^*_d$ are suprema over possibly empty sets; the statement is the pointwise bound for every admissible price, with the closed-form demands of p. 48.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), pp. 11–12, §4.1; closed forms of π*_a, π*_d in the proof of Lemma 10, p. 48

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- §4.1, pp. 11–12, with the case (a) and case (d) profits of the proof of Lemma 10, p. 48, at
`k = 0`: every price allowed in case (a) gives `λX/(X+1) · p ≤ λ(v − v̄)`, and every price allowed in
case (d) gives `λqX/(X+1) · p ≤ λqv`. -/
theorem case_a_d_bounds (P : Params) (hP : P.Standing) (hk : P.k = 0) (X : ℕ) (hX : 1 ≤ X) :
    (∀ p : ℝ, p ≤ pD P X 0 → P.lam * X / ((X : ℝ) + 1) * p ≤ P.lam * (P.v - P.vbar)) ∧
      (∀ p : ℝ, p ≤ pdUpper P X → P.lam * P.q * X / ((X : ℝ) + 1) * p ≤ P.lam * P.q * P.v) := by sorry
end BuyXFree.Threshold
