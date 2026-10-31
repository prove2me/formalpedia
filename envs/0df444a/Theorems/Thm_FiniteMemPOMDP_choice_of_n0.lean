-- Prove2me | Theorems.Thm_FiniteMemPOMDP_choice_of_n0
-- name    : FiniteMemPOMDP.choice_of_n0
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:35:11.472089+00:00
-- url     : https://prove2.me/theorems/c319dfa1-b21c-4286-bc71-f4610c6a421b
-- title:
--   §6.4 — choice of the block length $n_0$
-- statement:
--   Let $p^*\in\Delta(\mathcal K)$, let $\sigma$ be ergodic for $p^*$, let $\mathcal D^1,\dots,\mathcal D^J$ be the super-supports that occur with positive probability and $h^j$ a history with $\mathcal D^j=\mathcal B(h^j)$. For every $\varepsilon>0$ there exists $n_0\ge1$ such that for all $i\in[1..I]$, $j\in[1..J]$ and $k\in\mathcal D^j_i$,
--
--   $$\mathbb E^k_{\sigma[h^j]}\Big(\frac1{n_0}\sum_{m=1}^{n_0}G_m\Big)\ge\gamma^i_\infty-\varepsilon .$$
--
--   The paper derives this from Lemma 6.5 at the start of the construction of the block strategy.
--
--   Differences from the source:
--   - encoding: ∆(K), ∆(A) probability vectors; q: K × A → ∆(K × S); histories in ∪_m (A × S)^{m−1}; plays in (K × A × S)^ℕ; K, A, S finite → stdSimplex ℝ K / stdSimplex ℝ A; q as PMF (K × S); histories as chronological List (A × S); plays as ℕ → PlayStep A S K with coordinate n+1 = (A_{n+1}, S_{n+1}, K_{n+2}); K, A, S finite and nonempty; reason: Lean representations of the same objects; nonemptiness is implicit in the paper (p1 ∈ ∆(K), σ needs an action, q(k,a) ∈ ∆(K × S) needs a signal); the play space is a bijective re-indexing
--   - encoding: j ∈ [1 .. J], h^j with D^j = B(h^j) → histories h with P^{p*}_σ(H = h) > 0, D = superSuppTuple h, h^j = rep D for any rep with IsRepresentative; reason: the occurring super-supports are exactly the tuples B(h) of positive-probability histories; the paper's choice of h^j is arbitrary, so the statement holds for every choice
--   - encoding: classes i ∈ [1 .. I] → class values c ∈ ℝ; reason: empty components for non-values make those clauses vacuous
--   - encoding: B^i_m(h_m) defined by P^{k1}_σ(H_m = h_m) > 0 and P^{k1}_σ(K_m = k | H_m = h_m) > 0 → superSupp, {k | ∃ k1 ∈ K_i, 0 < P^{k1}_σ(H = h, K = k)}, indexed by the history alone; reason: the two conditions together say the joint probability is positive; the stage index is the history's length plus one
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, §6.4, p.18

import Mathlib
import Definitions.Def_FiniteMemPOMDP_IsErgodic
import Definitions.Def_FiniteMemPOMDP_IsRepresentative
import Definitions.Def_FiniteMemPOMDP_GoodBlockLength

namespace FiniteMemPOMDP

/-- **§6.4 — choice of the block length `n0`.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, §6.4, p.18: "Let ε > 0. By Lemma 6.5, there
exists n0 ∈ N∗ such that for all i ∈ [1 .. I], j ∈ [1 .. J] and k ∈ D^j_i,
E^k_{σ[hj]} ( (1/n0) ∑_{m=1}^{n0} Gm ) ≥ γ^i_∞ − ε."

Let `σ` be ergodic for `p∗` and let `rep` choose representative histories of the occurring
super-supports. For every `ε > 0` there is `n0 ≥ 1` with: for every super-support `D` that occurs,
every class value `c` and every `k ∈ D_c`, the expected average of the first `n0` rewards under
`σ[rep D]` started from `k` is at least `c − ε` (`GoodBlockLength`). -/
theorem choice_of_n0 {K A S : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype S] [DecidableEq S] [Nonempty S]
    (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A) (hσ : IsErgodic Γ p σ)
    (rep : (ℝ → Set K) → List (A × S)) (hrep : IsRepresentative Γ p σ rep)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n0 : ℕ, GoodBlockLength Γ p σ rep ε n0 := by sorry

end FiniteMemPOMDP
