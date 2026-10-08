-- Prove2me | Theorems.Thm_ChannelRebate_Effort_sec42_returns_optimum
-- name    : ChannelRebate.Effort.sec42_returns_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:36.804807+00:00
-- url     : https://prove2.me/theorems/96084251-b90a-4c05-91c4-c59fb192b590
-- title:
--   §4.2, p. 1000 — under returns alone, (e̲Q̲₀, e̲) is the retailer's unique optimum and R̲ = Λ(e̲)
-- statement:
--   Let $0<c<w<p$, $s<c$, $a>0$, let the return credit satisfy $b\in[s,w)$, and let $\xi\sim\mathrm{Uniform}(0,1)$, $V(e)=ae^2/2$. Under returns alone (no rebate, $u=0$, so the target $T$ plays no role) the retailer's profit is
--   $$R(Q,e)=-wQ+pE\min(Q,e\xi)+bE(Q-e\xi)^+-V(e).$$
--   Let $\underline Q_0>0$ solve $\Phi(\underline Q_0)=\frac{p-w}{p-b}$ and $\underline e=(p-b)\Gamma(\underline Q_0)/a$, the solution of $V'(\underline e)=(p-b)\Gamma(\underline Q_0)$. Then $(Q_2,\underline e)$ with $Q_2=\underline e\,\underline Q_0$ is the unique maximizer of $R$ over $Q\ge0$, $e\ge0$, and
--   $$\underline R=R(Q_2,\underline e)=\Lambda(\underline e).$$
--
--   This is the returns-only benchmark: the retailer's problem is the integrated channel's with $w$ for $c$ and $b$ for $s$. Its value is the retailer's profit $\underline L$ in Theorem 2.
--
--   **Formalization Note.** Specialised to the uniform instance of §4.3. The contract is written as $(w,u,b,T)$ with $u=0$ and an arbitrary $T$.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1000, §4.2 (returns alone: Q̲₀, Q₂, e̲, R̲ = Λ(e̲)), specialised to ξ ∼ Uniform(0, 1), V(e) = ae²/2 of p. 1001

import Mathlib
import Definitions.Def_ChannelRebate_Effort_Setting

open MeasureTheory Filter Topology

namespace ChannelRebate.Effort

theorem sec42_returns_optimum
    (p c s w a b T : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p) (hsc : s < c) (ha : 0 < a)
    (hsb : s ≤ b) (hbw : b < w)
    (Q0 : ℝ) (hQ0 : IsQlow0 p w b Q0) :
    optimalPairs (R p w 0 b a T) = {(elowOf p b a Q0 * Q0, elowOf p b a Q0)} ∧
      R p w 0 b a T (elowOf p b a Q0 * Q0) (elowOf p b a Q0) = Lam a (elowOf p b a Q0) := by sorry

end ChannelRebate.Effort
