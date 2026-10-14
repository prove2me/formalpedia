-- Prove2me | Theorems.Thm_AdvSellUpgrade_Online_proposition_5
-- name    : AdvSellUpgrade.Online.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:36.034839+00:00
-- url     : https://prove2.me/theorems/3ee7ee36-bd8b-4e45-87d1-d6f1b2823a68
-- title:
--   Proposition 5 (1)–(2), p. 17 — AS optimum when Bₛ − Bₐ < α(p(λₕ) − p(λₗ)): cutoffs (c(λₕ), c(λₗ)), Π^{AS⋆} = απ(λₕ) + (1−α)π(λₗ) + min{Bₐ, Bₛ}
-- statement:
--   Assume the standing assumptions $0<\lambda_l<\lambda_h<\mu$, $\bar c>0$, $0<\alpha<1$, and write $p_h=p(\lambda_h)$, $p_l=p(\lambda_l)$, $c_h=c(\lambda_h)$, $c_l=c(\lambda_l)$ and
--   $$V=\alpha\pi(\lambda_h)+(1-\alpha)\pi(\lambda_l)+\min\{B_a,B_s\}.$$
--   Consider the AS program (7).
--   1. If $B_s-B_a<0$, let $P_s^\star=B_s+p_h$ and $P_a^\star=B_s+\alpha p_h+(1-\alpha)p_l$.
--   2. If $0\le B_s-B_a<\alpha(p_h-p_l)$, let $P_s^\star=\dfrac{B_a-(1-\alpha)B_s}{\alpha}+p_h$ and $P_a^\star=B_a+\alpha p_h+(1-\alpha)p_l$.
--
--   In each case the point $(c_r,c_f,P_a,P_s)=(c_h,c_l,P_a^\star,P_s^\star)$ is feasible for (7), $P_a^\star<P_s^\star$, its objective value is $V$, the value $V$ is the maximum of (7),
--   $$\Pi^{AS\star}=\alpha\pi(\lambda_h)+(1-\alpha)\pi(\lambda_l)+\min\{B_a,B_s\},$$
--   and it is the only feasible point with objective value $V$.
--
--   So when the spot regular ticket is not much dearer than the advance one, advance selling with a cheaper advance fast-track ticket reaches the state-dependent pricing benchmark.
--
--   **Formalization Note** Only parts 1)–2) of Proposition 5 and the sentence "In the first two cases …" are formalized; parts 3)–4) involve the threshold $U$ of (D.14) and the root $c_r^\star(\alpha)$ of (D.6), which are defined implicitly in the appendix. "The optimal … are" is formalized as uniqueness of the optimal point. The maximum is stated as `IsGreatest` of the set of objective values of (7).
-- source:
--   Wang, Cao, Xie, Zhan, Advance Selling and Upgrading in Priority Queues, MSOM (2025), doi:10.1287/msom.2023.0410, p. 17, Proposition 5, parts 1)–2) and 'In the first two cases'; p. 16, (7)

import Mathlib
import Definitions.Def_AdvSellUpgrade_Online_Setting

namespace AdvSellUpgrade.Online

/-- Proposition 5, parts 1)–2) and "In the first two cases …", p. 17: when `Bs − Ba < 0`, resp.
`0 ≤ Bs − Ba < α(p(λh) − p(λl))`, the stated prices with cutoffs `(c(λh), c(λl))` are the unique
optimal solution of (7), `Pa⋆ < Ps⋆`, and the optimal value is `απ(λh) + (1 − α)π(λl) + min{Ba, Bs}`. -/
theorem proposition_5 (P : Params) (hP : P.Standing) :
    let ph := pFn P.mu P.cbar P.lamH
    let pl := pFn P.mu P.cbar P.lamL
    let ch := cFn P.mu P.cbar P.lamH
    let cl := cFn P.mu P.cbar P.lamL
    let V := P.alpha * piFn P.mu P.cbar P.lamH + (1 - P.alpha) * piFn P.mu P.cbar P.lamL
      + min P.Ba P.Bs
    (P.Bs - P.Ba < 0 →
      let PsS := P.Bs + ph
      let PaS := P.Bs + P.alpha * ph + (1 - P.alpha) * pl
      FeasAS P ch cl PaS PsS ∧ PaS < PsS ∧ objAS P ch cl PaS PsS = V ∧
        IsGreatest (asValues P) V ∧
        ∀ cr cf Pa Ps, FeasAS P cr cf Pa Ps → objAS P cr cf Pa Ps = V →
          cr = ch ∧ cf = cl ∧ Pa = PaS ∧ Ps = PsS) ∧
    (0 ≤ P.Bs - P.Ba → P.Bs - P.Ba < P.alpha * (ph - pl) →
      let PsS := (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha + ph
      let PaS := P.Ba + P.alpha * ph + (1 - P.alpha) * pl
      FeasAS P ch cl PaS PsS ∧ PaS < PsS ∧ objAS P ch cl PaS PsS = V ∧
        IsGreatest (asValues P) V ∧
        ∀ cr cf Pa Ps, FeasAS P cr cf Pa Ps → objAS P cr cf Pa Ps = V →
          cr = ch ∧ cf = cl ∧ Pa = PaS ∧ Ps = PsS) := by sorry

end AdvSellUpgrade.Online
