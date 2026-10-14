-- Prove2me | Theorems.Thm_AdvSellUpgrade_Online_proposition_6
-- name    : AdvSellUpgrade.Online.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:35.680613+00:00
-- url     : https://prove2.me/theorems/b7f7e59e-d005-4843-bd84-7d9fae58c0fa
-- title:
--   Proposition 6, pp. 18–19 — the AUS optimum: cutoffs (c(λₕ), c(λₗ)), Π^{AUS⋆} = απ(λₕ) + (1−α)π(λₗ) + min{Bₐ, Bₛ}
-- statement:
--   Assume the standing assumptions $0<\lambda_l<\lambda_h<\mu$, $\bar c>0$, $0<\alpha<1$; write $p_h=p(\lambda_h)$, $p_l=p(\lambda_l)$, $c_h=c(\lambda_h)$, $c_l=c(\lambda_l)$ and
--   $$V=\alpha\pi(\lambda_h)+(1-\alpha)\pi(\lambda_l)+\min\{B_a,B_s\}.$$
--   For the AUS program (8):
--   1. $V$ is the maximum of (8): $\Pi^{AUS\star}=\alpha\pi(\lambda_h)+(1-\alpha)\pi(\lambda_l)+\min\{B_a,B_s\}$;
--   2. every feasible point with objective value $V$ has cutoffs $c_r=c_h$ and $c_f=c_l$;
--   3. if $B_s-B_a<0$: for every $K\ge\max\{0,\ (B_s-B_a)/\alpha+p_h,\ B_s-B_a+\alpha p_h+(1-\alpha)p_l\}$, the point with $P_a=\alpha p_h+(1-\alpha)p_l+B_s$, $P_s=p_h+B_s$ and fee $K$ is feasible with value $V$;
--   4. if $0\le B_s-B_a<\alpha(p_h-p_l)$: with $P_a=\alpha p_h+(1-\alpha)p_l+B_a$, both $P_s=p_h+(B_a-(1-\alpha)B_s)/\alpha$ with any $K\ge p_h$, and $K=p_h$ with any $P_s\ge p_h+(B_a-(1-\alpha)B_s)/\alpha$, are feasible with value $V$;
--   5. if $B_s-B_a\ge\alpha(p_h-p_l)$: $P_a=\alpha p_h+(1-\alpha)p_l+B_a$, $K=p_h$ and any $P_s\ge P_a$ are feasible with value $V$.
--
--   With the upgrading option the seller always reaches the state-dependent pricing benchmark, whatever the regular prices.
--
--   **Formalization Note** "The upgrading fee can be any value $K$ satisfying …" and the families in 2)–3) of the paper are read as "every such price vector is optimal"; the statement does not claim that these are all optimal price vectors. "The optimal delay sensitivity cutoffs are" is formalized as item 2. The fourth constraint of (8) is read with $W^l$ (see the definition file); it binds only at $c_f=\bar c$ and does not affect this result.
-- source:
--   Wang, Cao, Xie, Zhan, Advance Selling and Upgrading in Priority Queues, MSOM (2025), doi:10.1287/msom.2023.0410, pp. 18–19, Proposition 6; p. 18, (8)

import Mathlib
import Definitions.Def_AdvSellUpgrade_Online_Setting

namespace AdvSellUpgrade.Online

/-- Proposition 6, pp. 18–19: the optimal value of (8) is `απ(λh) + (1 − α)π(λl) + min{Ba, Bs}`, every
optimal solution has cutoffs `(c(λh), c(λl))`, and in each of the three price regimes every listed price
vector is feasible and optimal. -/
theorem proposition_6 (P : Params) (hP : P.Standing) :
    let ph := pFn P.mu P.cbar P.lamH
    let pl := pFn P.mu P.cbar P.lamL
    let ch := cFn P.mu P.cbar P.lamH
    let cl := cFn P.mu P.cbar P.lamL
    let V := P.alpha * piFn P.mu P.cbar P.lamH + (1 - P.alpha) * piFn P.mu P.cbar P.lamL
      + min P.Ba P.Bs
    IsGreatest (ausValues P) V ∧
    (∀ cr cf Pa Ps K, FeasAUS P cr cf Pa Ps K → objAUS P cr cf Pa Ps K = V →
      cr = ch ∧ cf = cl) ∧
    (P.Bs - P.Ba < 0 →
      ∀ K, max 0 (max ((P.Bs - P.Ba) / P.alpha + ph)
          (P.Bs - P.Ba + P.alpha * ph + (1 - P.alpha) * pl)) ≤ K →
        FeasAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Bs) (ph + P.Bs) K ∧
          objAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Bs) (ph + P.Bs) K = V) ∧
    (0 ≤ P.Bs - P.Ba → P.Bs - P.Ba < P.alpha * (ph - pl) →
      (∀ K, ph ≤ K →
        FeasAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba)
            (ph + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha) K ∧
          objAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba)
            (ph + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha) K = V) ∧
      (∀ Ps, ph + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha ≤ Ps →
        FeasAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba) Ps ph ∧
          objAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba) Ps ph = V)) ∧
    (P.alpha * (ph - pl) ≤ P.Bs - P.Ba →
      ∀ Ps, P.alpha * ph + (1 - P.alpha) * pl + P.Ba ≤ Ps →
        FeasAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba) Ps ph ∧
          objAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba) Ps ph = V) := by sorry

end AdvSellUpgrade.Online
