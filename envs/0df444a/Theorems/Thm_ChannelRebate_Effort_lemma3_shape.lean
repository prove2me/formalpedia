-- Prove2me | Theorems.Thm_ChannelRebate_Effort_lemma3_shape
-- name    : ChannelRebate.Effort.lemma3_shape
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:09.815873+00:00
-- url     : https://prove2.me/theorems/7283d351-6052-4539-9129-10bfab5df6d0
-- title:
--   Lemma 3, p. 1001 — A(·|T) is concave on [0, T/τ), and convex-then-concave or concave on (T/τ, ∞) according as T < uτ³/a or T ≥ uτ³/a
-- statement:
--   In the setting of Lemma 2 ($0<c<w<p$, $s<c$, $a>0$, $u>0$, $b\in[s,w)$, $T>0$), let $\xi\sim\mathrm{Uniform}(0,1)$, $V(e)=ae^2/2$, let $\tau$ be the threshold of §4.3 and $A(e\mid T)=\max_{Q\ge0}R(Q,e\mid T)$. Write $\bar\gamma=[uT^2/a]^{1/3}$.
--
--   1. If $T<u\tau^3/a$, then $A(\cdot\mid T)$ is strictly concave on $[0,T/\tau)$ and on $(\bar\gamma,\infty)$, and strictly convex on $(T/\tau,\bar\gamma)$.
--   2. If $T\ge u\tau^3/a$, then $A(\cdot\mid T)$ is strictly concave on $[0,T/\tau)$ and on $(T/\tau,\infty)$.
--
--   Together with $A(e\mid T)\to-\infty$, this gives one maximizer of $A(\cdot\mid T)$ on $[0,T/\tau]$ and at most one on $(T/\tau,\infty)$.
--
--   **Formalization Note.** "Concave" and "convex" are strict, following the convention of p. 995 ("All functions described as concave, convex, increasing, or decreasing are strictly so"). The cube root is the real power $(uT^2/a)^{1/3}$ of a positive number.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1001, Lemma 3; proof p. 1005

import Mathlib
import Definitions.Def_ChannelRebate_Effort_Setting

open MeasureTheory Filter Topology

namespace ChannelRebate.Effort

theorem lemma3_shape
    (p c s w a u b T : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p) (hsc : s < c) (ha : 0 < a)
    (hu : 0 < u) (hsb : s ≤ b) (hbw : b < w) (hT : 0 < T)
    (τ : ℝ) (hτ : IsTau p w u b τ) :
    (T < u * τ ^ 3 / a →
        StrictConcaveOn ℝ (Set.Ico 0 (T / τ)) (Aeff p w u b a T) ∧
        StrictConcaveOn ℝ (Set.Ioi ((u * T ^ 2 / a) ^ ((1 : ℝ) / 3))) (Aeff p w u b a T) ∧
        StrictConvexOn ℝ (Set.Ioo (T / τ) ((u * T ^ 2 / a) ^ ((1 : ℝ) / 3))) (Aeff p w u b a T)) ∧
      (u * τ ^ 3 / a ≤ T →
        StrictConcaveOn ℝ (Set.Ico 0 (T / τ)) (Aeff p w u b a T) ∧
        StrictConcaveOn ℝ (Set.Ioi (T / τ)) (Aeff p w u b a T)) := by sorry

end ChannelRebate.Effort
