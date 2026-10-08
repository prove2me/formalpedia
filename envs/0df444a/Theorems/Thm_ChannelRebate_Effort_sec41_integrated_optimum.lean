-- Prove2me | Theorems.Thm_ChannelRebate_Effort_sec41_integrated_optimum
-- name    : ChannelRebate.Effort.sec41_integrated_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:08.89149+00:00
-- url     : https://prove2.me/theorems/bf7134f8-08a1-4fac-920b-84f5b71342f2
-- title:
--   §4.1, p. 999 — under ξ ∼ U(0,1), V = ae²/2, (ēQ̄₀, ē) is the unique maximizer of Π(Q, e) and Π = Λ(ē)
-- statement:
--   Let $0<c<p$, $s<c$ and $a>0$, let $\xi\sim\mathrm{Uniform}(0,1)$ and $V(e)=ae^2/2$. Let $\bar Q_0>0$ solve $\Phi(\bar Q_0)=\frac{p-c}{p-s}$ and put $\bar e=(p-s)\Gamma(\bar Q_0)/a$, the solution of $V'(\bar e)=(p-s)\Gamma(\bar Q_0)$. Then the integrated channel's profit
--   $$\Pi(Q,e)=-cQ+pE\min(Q,e\xi)+sE(Q-e\xi)^+-V(e)$$
--   has exactly one maximizer over $Q\ge0$, $e\ge0$, namely $(\bar Q,\bar e)$ with $\bar Q=\bar e\bar Q_0$, and the maximum value is
--   $$\Pi=\Pi(\bar Q,\bar e)=\Lambda(\bar e)=\bar e V'(\bar e)-V(\bar e).$$
--
--   This is the integrated-channel benchmark against which coordination in Theorem 2 is measured.
--
--   **Formalization Note.** The paper states the first-order conditions for general $\xi$ and $V$ and assumes an optimum exists. Here the claim is specialised to the instance of §4.3 ($\xi\sim\mathrm{Uniform}(0,1)$, $V(e)=ae^2/2$), where existence holds and the optimum is unique. The pair is written in the order $(Q,e)$.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 999, §4.1 (first-order conditions and Π = Λ(ē)), specialised to ξ ∼ Uniform(0, 1), V(e) = ae²/2 of p. 1001

import Mathlib
import Definitions.Def_ChannelRebate_Effort_Setting

open MeasureTheory Filter Topology

namespace ChannelRebate.Effort

theorem sec41_integrated_optimum
    (p c s a : ℝ) (hc : 0 < c) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (Qb : ℝ) (hQb : IsQbar0 p c s Qb) :
    optimalPairs (Pi_ p c s a) = {(ebarOf p s a Qb * Qb, ebarOf p s a Qb)} ∧
      Pi_ p c s a (ebarOf p s a Qb * Qb) (ebarOf p s a Qb) = Lam a (ebarOf p s a Qb) := by sorry

end ChannelRebate.Effort
