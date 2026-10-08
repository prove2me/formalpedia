-- Prove2me | Theorems.Thm_ChannelRebate_Effort_lemma4_optimal_effort
-- name    : ChannelRebate.Effort.lemma4_optimal_effort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:00.481118+00:00
-- url     : https://prove2.me/theorems/45ef891d-c0a4-4a4e-8c42-9b4db8ec8bff
-- title:
--   Lemma 4, p. 1001 — ϒ exists uniquely; the optimal effort is ê > T/τ if T < ϒ, e̲ < T/τ if T > ϒ, and both if T = ϒ
-- statement:
--   In the setting of Lemma 2 ($0<c<w<p$, $s<c$, $a>0$, $u>0$, $b\in[s,w)$, $T>0$), let $\xi\sim\mathrm{Uniform}(0,1)$, $V(e)=ae^2/2$, $A(e\mid T)=\max_{Q\ge0}R(Q,e\mid T)$, and let $\underline e=(p-b)\Gamma(\underline Q_0)/a$. For a target $T'$ write $\underline A(\tilde e\mid T')=\max_{[0,T'/\tau]}A(\cdot\mid T')$ and $\bar A(\hat e\mid T')=\max_{[T'/\tau,\infty)}A(\cdot\mid T')$, and define on $[\tau\underline e,\infty)$
--   $$j(T')=\underline A(\tilde e\mid T')-\bar A(\hat e\mid T').$$
--   Let $e^*$ be the set of maximizers of $A(\cdot\mid T)$ over $e\ge0$.
--
--   1. **(a)** There is exactly one $\Upsilon\ge\tau\underline e$ with $j(\Upsilon)=0$ (and both maxima exist there).
--   2. **(b)** For this $\Upsilon$:
--      - if $T<\Upsilon$, then $e^*=\{\hat e\}$ for a single $\hat e>T/\tau$;
--      - if $T>\Upsilon$, then $e^*=\{\underline e\}$ and $\underline e<T/\tau$;
--      - if $T=\Upsilon$, then $e^*=\{\hat e,\underline e\}$ with $\underline e<T/\tau<\hat e$.
--
--   The threshold $\Upsilon$ plays for effort the role that $\tau_0$ plays for quantity in Lemma 1: a target above it is ignored, a target below it raises effort.
--
--   **Formalization Note.** The paper's $\hat e$ is the maximizer of $A(\cdot\mid T)$ on $(T/\tau,\infty)$, or $T/\tau$ if there is none, and $\tilde e$ the maximizer on $[0,T/\tau]$; $\bar A(\hat e\mid T')$ is therefore the maximum of $A(\cdot\mid T')$ on $[T'/\tau,\infty)$, which is how $j$ is encoded (the relation `IsJ`, with existence of both maxima built in). In (b) a maximizer of $A$ above $T/\tau$ is necessarily $\hat e$, so the statement asserts $e^*=\{\hat e\}$ in the form "$e^*$ is a single point $\hat e>T/\tau$". No `Classical.choose` is used.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1001, Lemma 4 and the definitions of ẽ, ê, A̲, Ā, j, ϒ just before it; proof p. 1005

import Mathlib
import Definitions.Def_ChannelRebate_Effort_Setting

open MeasureTheory Filter Topology

namespace ChannelRebate.Effort

theorem lemma4_optimal_effort
    (p c s w a u b T : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p) (hsc : s < c) (ha : 0 < a)
    (hu : 0 < u) (hsb : s ≤ b) (hbw : b < w) (hT : 0 < T)
    (Q0 τ : ℝ) (hQ0 : IsQlow0 p w b Q0) (hτ : IsTau p w u b τ) :
    (∃! Υ : ℝ, τ * elowOf p b a Q0 ≤ Υ ∧ IsJ p w u b a τ Υ 0) ∧
      ∀ Υ : ℝ, τ * elowOf p b a Q0 ≤ Υ → IsJ p w u b a τ Υ 0 →
        (T < Υ → ∃ eh, T / τ < eh ∧ optimalSet (Aeff p w u b a T) = {eh}) ∧
        (Υ < T → optimalSet (Aeff p w u b a T) = {elowOf p b a Q0} ∧
          elowOf p b a Q0 < T / τ) ∧
        (T = Υ → ∃ eh, T / τ < eh ∧ optimalSet (Aeff p w u b a T) = {eh, elowOf p b a Q0} ∧
          elowOf p b a Q0 < T / τ) := by sorry

end ChannelRebate.Effort
