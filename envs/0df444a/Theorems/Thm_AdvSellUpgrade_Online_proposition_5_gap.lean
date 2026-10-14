-- Prove2me | Theorems.Thm_AdvSellUpgrade_Online_proposition_5_gap
-- name    : AdvSellUpgrade.Online.proposition_5_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:32.782973+00:00
-- url     : https://prove2.me/theorems/a40ec662-515e-40fc-a834-59b6342b55bb
-- title:
--   Proposition 5 (last sentence), p. 17 — if Bₛ − Bₐ > α(p(λₕ) − p(λₗ)), Π^{AS⋆} < απ(λₕ) + (1−α)π(λₗ) + Bₐ
-- statement:
--   Assume the standing assumptions $0<\lambda_l<\lambda_h<\mu$, $\bar c>0$, $0<\alpha<1$. If
--   $$B_s-B_a>\alpha\bigl(p(\lambda_h)-p(\lambda_l)\bigr),$$
--   then there is a number $v$ with
--   $$v<\alpha\pi(\lambda_h)+(1-\alpha)\pi(\lambda_l)+B_a$$
--   such that every feasible point of the AS program (7) has objective value at most $v$. In particular the optimal AS revenue $\Pi^{AS\star}$ falls strictly short of the state-dependent pricing benchmark.
--
--   This is the half of the comparison in Theorem 1 that makes upgrading strictly profitable when the spot regular ticket is much dearer than the advance one.
--
--   **Formalization Note** The paper states this for "the last two cases", i.e. $B_s-B_a\ge\alpha(p(\lambda_h)-p(\lambda_l))$. At equality the point of part 2) of Proposition 5 is feasible (with $P_a^\star=P_s^\star$) and attains the bound, so the printed claim fails there; it is stated for the strict inequality, which is how the proof of Theorem 1 (Online Appendix p. 13) uses it. The uniform gap ("some $v$ below the bound") expresses that the supremum, not only each value, is below the bound; attainment of the AS optimum is not asserted.
-- source:
--   Wang, Cao, Xie, Zhan, Advance Selling and Upgrading in Priority Queues, MSOM (2025), doi:10.1287/msom.2023.0410, p. 17, Proposition 5, last sentence; Online Appendix p. 13, proof of Theorem 1, case (iii)

import Mathlib
import Definitions.Def_AdvSellUpgrade_Online_Setting

namespace AdvSellUpgrade.Online

/-- Proposition 5, last sentence, p. 17 (boundary repaired): if `Bs − Ba > α(p(λh) − p(λl))`, the
supremum of (7) lies strictly below `απ(λh) + (1 − α)π(λl) + Ba`. -/
theorem proposition_5_gap (P : Params) (hP : P.Standing)
    (hgap : P.alpha * (pFn P.mu P.cbar P.lamH - pFn P.mu P.cbar P.lamL) < P.Bs - P.Ba) :
    ∃ v : ℝ, v < P.alpha * piFn P.mu P.cbar P.lamH + (1 - P.alpha) * piFn P.mu P.cbar P.lamL + P.Ba ∧
      ∀ cr cf Pa Ps, FeasAS P cr cf Pa Ps → objAS P cr cf Pa Ps ≤ v := by sorry

end AdvSellUpgrade.Online
