-- Prove2me | Theorems.Thm_FlexLearning_Threshold_vF_closed_form_x0
-- name    : FlexLearning.Threshold.vF_closed_form_x0
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T11:47:19.881802+00:00
-- url     : https://prove2.me/theorems/4b7b3ae4-c2c4-4d47-8107-ef8d1b944821
-- title:
--   Proof of Proposition 1, pp. A6–A7 — closed form of the flexible two-period objective v_F at x = 0 (three capacity regimes)
-- statement:
--   Take the two-product, two-period model with $\xi=0$ and first-period demands i.i.d. uniform on $[0,U]$ ($x=0$, $U>0$). Let $p$ be the price, $c$ the dedicated unit cost ($0\le c<p$), $c_F$ the flexible unit cost, and $\Delta=(p-c)(p+c)+cp$. The two-period objective of the flexible system, $v_F(Q_F)$ (first-period flexible profit plus expected optimal second-period dedicated profit under the censored-sales posteriors), has the closed form
--   $$v_F(Q_F)=\begin{cases}\dfrac{(p-c)^2U}{p}+Q_F\Big(\dfrac{\Delta}{p}-c_F\Big)-\dfrac{\Delta\,Q_F^3}{6U^2p}, & 0\le Q_F\le U,\\[8pt] 2U(p-c_F)-Uc+c_F(2U-Q_F)-\dfrac{\Delta\,(2U-Q_F)^3}{6U^2p}, & U\le Q_F\le 2U,\\[8pt] pU-c_FQ_F+(p-c)U, & Q_F\ge 2U.\end{cases}$$
--
--   The three pieces are the regimes of the proof of Proposition 1 at $x=0$. For $Q_F\ge U$ product 1's demand is always observed (case $j=1$; the middle formula is the $x=0$ instance of $v_{F,1}$). For $Q_F\le U$ product 1 may stock out, and then product 2 receives no capacity. Maximising $v_F$ gives $V_F(c_F)$, which is compared with $V_N$ in Proposition 1.
--
--   **Formalization Note.** $U>0$ and $0\le c<p$ are assumed. The pieces agree at $Q_F=U$ and $Q_F=2U$.
-- source:
--   Chod, Markakis & Trichakis, On the Learning Benefits of Resource Flexibility, SSRN preprint 3212177 (version of December 6, 2019), proof of Proposition 1, pp. A6–A7 (cases j = 1 and j = 3 for x = 0; v_F via Lemma 3)

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model

namespace FlexLearning.Threshold

theorem vF_closed_form_x0 (p c U cF Q : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hU : 0 < U) :
    (0 ≤ Q → Q ≤ U → vF p c 0 U cF Q = (p - c) ^ 2 * U / p +
      Q * (((p - c) * (p + c) + c * p) / p - cF) -
      ((p - c) * (p + c) + c * p) * Q ^ 3 / (6 * U ^ 2 * p)) ∧
    (U ≤ Q → Q ≤ 2 * U → vF p c 0 U cF Q = 2 * U * (p - cF) - U * c + cF * (2 * U - Q) -
      ((p - c) * (p + c) + c * p) * (2 * U - Q) ^ 3 / (6 * U ^ 2 * p)) ∧
    (2 * U ≤ Q → vF p c 0 U cF Q = p * U - cF * Q + (p - c) * U) := by sorry

end FlexLearning.Threshold
