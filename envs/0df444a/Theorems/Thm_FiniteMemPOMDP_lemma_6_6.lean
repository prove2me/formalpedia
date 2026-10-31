-- Prove2me | Theorems.Thm_FiniteMemPOMDP_lemma_6_6
-- name    : FiniteMemPOMDP.lemma_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:48.076601+00:00
-- url     : https://prove2.me/theorems/7ae5e2e2-e063-46c5-b0a0-b2bb7c2bd8f4
-- title:
--   Lemma 6.6 (Continuation super-support)
-- statement:
--   Let $\mathcal K_i$ be a value class and let $h=(h_m,h_{m'})$ be a history. Write $\mathcal C=\mathcal B^i(h)$ for the super-support component after $h$. Then for every $k\in\mathcal B^i(h_m)$,
--
--   $$\mathbb P^k_{\sigma[h_m]}\big(K_{m'}\in\mathcal C\mid H_{m'}=h_{m'}\big)=1 .$$
--
--   The super-support after $m+m'$ stages coincides with the one obtained by first advancing $m$ stages and then playing the continuation $\sigma[h_m]$ for $m'$ stages. The property does not use ergodicity (Remark 6.7); the Lean statement holds for an arbitrary set $K_0$ of initial states in place of $\mathcal K_i$ and for any strategy $\sigma$.
--
--   Differences from the source:
--   - encoding: ∆(K), ∆(A) probability vectors; q: K × A → ∆(K × S); histories in ∪_m (A × S)^{m−1}; plays in (K × A × S)^ℕ; K, A, S finite → stdSimplex ℝ K / stdSimplex ℝ A; q as PMF (K × S); histories as chronological List (A × S); plays as ℕ → PlayStep A S K with coordinate n+1 = (A_{n+1}, S_{n+1}, K_{n+2}); K, A, S finite and nonempty; reason: Lean representations of the same objects; nonemptiness is implicit in the paper (p1 ∈ ∆(K), σ needs an action, q(k,a) ∈ ∆(K × S) needs a signal); the play space is a bijective re-indexing
--   - generalization: the value class K_i of an ergodic σ → an arbitrary set K₀ ⊆ K and an arbitrary σ; reason: Remark 6.7: the property does not use ergodicity; K₀ = K_i gives the lemma
--   - encoding: P^k_{σ[h_m]}(K_{m′} ∈ C | H_{m′} = h_{m′}) = 1 → P^k_{σ[h]}(H = h′ ∧ K ∉ C) = 0; reason: equivalent when P(H = h′) > 0; the conditional probability is undefined otherwise
--   - encoding: (h_m, h_{m′}) ∈ H_{m+m′}, C = B^i_{m+m′} → h ++ h′, superSupp … (h ++ h′); reason: histories indexed by length; the paper's stage index of the concatenation is off by one, the object is the same
--   - encoding: B^i_m(h_m) defined by P^{k1}_σ(H_m = h_m) > 0 and P^{k1}_σ(K_m = k | H_m = h_m) > 0 → superSupp, {k | ∃ k1 ∈ K_i, 0 < P^{k1}_σ(H = h, K = k)}, indexed by the history alone; reason: the two conditions together say the joint probability is positive; the stage index is the history's length plus one
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Lemma 6.6, p.17

import Mathlib
import Definitions.Def_FiniteMemPOMDP_superSupp
import Definitions.Def_FiniteMemPOMDP_shift

namespace FiniteMemPOMDP

/-- **Lemma 6.6 (Continuation super-support).**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Lemma 6.6, p.17: "Let i ∈ [1 .. I], m, m′ ≥ 0.
For all realizations Hm+m′ = h = (hm, hm′) ∈ Hm+m′, denoting C = B^i_{m+m′}(hm+m′), we have that, for
all k ∈ B^i_m(hm), P^k_{σ[hm]}(Km′ ∈ C|Hm′ = hm′) = 1." Remark 6.7: "This property does not depend
on the fact that σ is ergodic for p∗."

For every set `K₀` of initial states, all histories `h`, `h'` and every `k` reachable after `h`
from `K₀` (`k ∈ superSupp Γ σ K₀ h`): under the shifted strategy `σ[h]` started from `k`, the event
"the history is `h'` and the state after it is not reachable after `h ++ h'` from `K₀`" has
probability zero.

**Formalization Note** The conditional probability `P(· | H = h')` is undefined when
`P(H = h') = 0`; "`P(K ∈ C | H = h') = 1`" is stated as `P(H = h', K ∉ C) = 0`, which is equivalent
when `P(H = h') > 0`. Histories are indexed by length, so `(hm, hm′)` is `h ++ h'` and `K_{m′}`
is the state after `h'`. The set `K₀` is arbitrary (the paper takes a value class `K_i`;
Remark 6.7). -/
theorem lemma_6_6 {K A S : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype S] [DecidableEq S] [Nonempty S]
    (Γ : POMDP K A S) (σ : List (A × S) → A) (K₀ : Set K) (h h' : List (A × S)) (k : K)
    (hk : k ∈ superSupp Γ σ K₀ h) :
    lawOfPlays Γ (pointBelief k) (shift σ h)
      {ω | historyAt h'.length ω = h' ∧ stateAt h'.length ω ∉ superSupp Γ σ K₀ (h ++ h')} = 0 := by sorry

end FiniteMemPOMDP
