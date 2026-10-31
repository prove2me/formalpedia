-- Prove2me | Theorems.Thm_DeliveryDisclosure_InfoEffort_eq_10
-- name    : DeliveryDisclosure.InfoEffort.eq_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:21.263582+00:00
-- url     : https://prove2.me/theorems/00daf869-bba2-4c52-9ea1-7358c523aaff
-- title:
--   Eq. (10), p. 10 — the demand rate never exceeds the maximum market share times the market size, λ ≤ S̄Λ
-- statement:
--   Under the standing assumptions, let $\phi\in[0,1]$, and let $(p,t)$ be a plan with $p\ge c$ and $t\ge 0$. Then the demand rate is at most the maximum market share times the market size:
--   $$\lambda(p,t,\phi)\;\le\;\bar S(\phi)\,\Lambda,\qquad \bar S(\phi)=\frac{1}{1+\exp[-(\bar V-V_e)/\omega_\theta(\phi)]},\quad \bar V=\alpha-c+\beta_r\rho.$$
--
--   The bound holds because $V\le\bar V$ whenever $p\ge c$, $q\le 1$ and $t\ge 0$. It is what makes the capacity condition (16) meaningful: the queue is stable at every plan.
--
--   **Formalization Note** The page calls $\bar V$ a lower bound of $V$ (p. 9); it is an upper bound, and eq. (10) uses it as such. The shortest delivery time is $\underline t=0$.
-- source:
--   Leng, Becerril-Arreola, Parlar & Ferguson, Disclosing Delivery Performance Information (authors' preprint, April 2nd, 2023), p. 10, eq. (10); V̄ from p. 9

import Mathlib
import Definitions.Def_DeliveryDisclosure_InfoEffort_Model

namespace DeliveryDisclosure.InfoEffort

/-- Eq. (10), p. 10: at every plan with `p ≥ c` and `t ≥ 0` the demand rate is at most
the maximum share times the market size, `λ(p, t, ϕ) ≤ S̄ Λ`. -/
theorem eq_10 (P : Params) (hP : Standing P) (p t ϕ : ℝ) (hϕ : ϕ ∈ Set.Icc (0 : ℝ) 1)
    (hp : P.c ≤ p) (ht : 0 ≤ t) :
    dem P p t ϕ ≤ Sbar P ϕ * P.Λ := by sorry

end DeliveryDisclosure.InfoEffort
