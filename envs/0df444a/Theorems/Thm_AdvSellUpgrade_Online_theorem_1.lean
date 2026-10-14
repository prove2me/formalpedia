-- Prove2me | Theorems.Thm_AdvSellUpgrade_Online_theorem_1
-- name    : AdvSellUpgrade.Online.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:40.031117+00:00
-- url     : https://prove2.me/theorems/8c2742e1-285f-4675-af25-fd0055db781b
-- title:
--   Theorem 1, p. 19 — with all customers online, Π^{AS⋆} = Π^{AUS⋆} iff Bₛ − Bₐ ≤ α(p(λₕ) − p(λₗ)); otherwise Π^{AUS⋆} > Π^{AS⋆}
-- statement:
--   Consider a single server with a fast-track and a regular queue, service rate $\mu$, arrival rate $\lambda_h$ on crowded and $\lambda_l$ on uncrowded days, delay costs uniform on $[0,\bar c]$, and a probability $\alpha$ that a customer arrives on a crowded day, with
--   $$0<\lambda_l<\lambda_h<\mu,\qquad \bar c>0,\qquad 0<\alpha<1,$$
--   and arbitrary regular-ticket prices $B_a$ (advance) and $B_s$ (spot). All customers are online. Let $\Pi^{AS\star}$ be the optimal value of the advance-and-spot-selling program (7) and $\Pi^{AUS\star}$ that of the program (8), which adds an upgrading fee. Let $p(\lambda)=\bigl(\mu-\sqrt{\mu(\mu-\lambda)}\bigr)\lambda\bar c/((\mu-\lambda)\mu^2)$.
--
--   Then the supremum $\Pi^{AS\star}$ of (7) exists, the maximum $\Pi^{AUS\star}$ of (8) exists and is attained, and
--   $$\Pi^{AS\star}=\Pi^{AUS\star}\quad\text{if } B_s-B_a\le\alpha\bigl(p(\lambda_h)-p(\lambda_l)\bigr),\qquad \Pi^{AUS\star}>\Pi^{AS\star}\quad\text{if } B_s-B_a>\alpha\bigl(p(\lambda_h)-p(\lambda_l)\bigr).$$
--
--   Upgrading is therefore worthless when the spot regular ticket is cheaper, or only slightly dearer, than the advance one, and strictly profitable exactly when the spot regular premium exceeds $\alpha(p(\lambda_h)-p(\lambda_l))$.
--
--   **Formalization Note** The printed statement has "$<$" in the equality case and "Otherwise" for the strict one. At $B_s-B_a=\alpha(p(\lambda_h)-p(\lambda_l))$ the advance-selling program attains the upgrading optimum, so the printed strict claim is false there; the boundary is put in the equality case, as in the paper's proof (Online Appendix p. 13, case (ii): $0<B_s-B_a\le\alpha(p(\lambda_h)-p(\lambda_l))$). This strengthens the printed equality case. $\Pi^{AS\star}$ is stated as a least upper bound (attainment of the AS optimum in the strict case is not claimed by the theorem) and $\Pi^{AUS\star}$ as a greatest element; neither is a bare supremum. The theorem is about the reduced programs (7) and (8); their derivation from the queueing game is not formalized. $\alpha$ is a free parameter in $(0,1)$; at $\alpha=1$ the strict claim fails. The fourth constraint of (8) is read with $W^l$.
-- source:
--   Wang, Cao, Xie, Zhan, Advance Selling and Upgrading in Priority Queues, MSOM (2025), doi:10.1287/msom.2023.0410, p. 19, Theorem 1; Online Appendix p. 13, proof of Theorem 1

import Mathlib
import Definitions.Def_AdvSellUpgrade_Online_Setting

namespace AdvSellUpgrade.Online

/-- Theorem 1, p. 19 (boundary repaired): with all customers online, the AS program (7) has a least upper
bound `vAS` and the AUS program (8) a maximum `vAUS`; they are equal when
`Bs − Ba ≤ α(p(λh) − p(λl))`, and `vAS < vAUS` when `Bs − Ba > α(p(λh) − p(λl))`. -/
theorem theorem_1 (P : Params) (hP : P.Standing) :
    ∃ vAS vAUS : ℝ, IsLUB (asValues P) vAS ∧ IsGreatest (ausValues P) vAUS ∧
      (P.Bs - P.Ba ≤ P.alpha * (pFn P.mu P.cbar P.lamH - pFn P.mu P.cbar P.lamL) → vAS = vAUS) ∧
      (P.alpha * (pFn P.mu P.cbar P.lamH - pFn P.mu P.cbar P.lamL) < P.Bs - P.Ba →
        vAS < vAUS) := by sorry

end AdvSellUpgrade.Online
