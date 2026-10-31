-- Prove2me | Theorems.Thm_FiniteMemPOMDP_lemma_6_8
-- name    : FiniteMemPOMDP.lemma_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:54.350528+00:00
-- url     : https://prove2.me/theorems/e9152528-1856-438e-bad8-8d6f2db4ab08
-- title:
--   Lemma 6.8 — the block strategy tracks the super-support
-- statement:
--   Let $p^*\in\Delta(\mathcal K)$, let $\sigma$ be ergodic for $p^*$, let $\sigma'$ be the block strategy of §6.4 with block length $n_0\ge1$, and let $\mathcal D^{J_\ell}$ be the super-support in force at stage $\ell n_0+1$. Then:
--
--   1. for every class $i$, every $k\in\mathcal K_i$ and every $\ell\ge0$, $$\mathbb P^k_{\sigma'}\big(K_{\ell n_0+1}\in\mathcal D^{J_\ell}_i\big)=1;$$
--   2. consequently $\mathcal D^{J_\ell}=(\mathcal D^{J_\ell}_1,\dots,\mathcal D^{J_\ell}_I)$ is a partition of the support of the belief $P_{\ell n_0+1}$ (almost surely under $\mathbb P^{p^*}_{\sigma'}$): its components are pairwise disjoint and their union is the support;
--   3. moreover, for every class $i$ and every $\ell\ge0$, $$\mathbb P^{p^*}_{\sigma'}\big(K_{\ell n_0+1}\in\mathcal D^{J_\ell}_i\big)=p^*(\mathcal K_i).$$
--
--   Differences from the source:
--   - encoding: ∆(K), ∆(A) probability vectors; q: K × A → ∆(K × S); histories in ∪_m (A × S)^{m−1}; plays in (K × A × S)^ℕ; K, A, S finite → stdSimplex ℝ K / stdSimplex ℝ A; q as PMF (K × S); histories as chronological List (A × S); plays as ℕ → PlayStep A S K with coordinate n+1 = (A_{n+1}, S_{n+1}, K_{n+2}); K, A, S finite and nonempty; reason: Lean representations of the same objects; nonemptiness is implicit in the paper (p1 ∈ ∆(K), σ needs an action, q(k,a) ∈ ∆(K × S) needs a signal); the play space is a bijective re-indexing
--   - reading: D^{Jℓ} is a partition of the support of P_{ℓn0+1} → a.s., the components are pairwise disjoint and their union equals {k | P_{ℓn0+1}(k) > 0}; components may be empty; reason: the reading with nonempty parts is false: K = {x, y}, one action, q(x,a) = δ_(x,s_x), q(y,a) = δ_(y,s_y), g(x,a) = 1, g(y,a) = 0, p* = (1/2, 1/2), σ ≡ a is ergodic and, for ℓ = 1, D^{J_1} = ({x}, ∅) with probability 1/2; the paper's proof shows disjointness and cover
--   - generalization: σ′ built with the n0 chosen in §6.4 → every n0 ≥ 1; reason: the lemma's proof does not use the choice of n0; the chosen n0 is one instance
--   - encoding: J_ℓ ∈ [1 .. J], h^{J_ℓ}; classes i ∈ [1 .. I] → the tuple blockTuple … ℓ itself, rep with IsRepresentative; class values c ∈ ℝ; reason: same strategy on positive-probability histories; for a non-value c the class and every component are empty and the clauses hold trivially
--   - encoding: B^i_m(h_m) defined by P^{k1}_σ(H_m = h_m) > 0 and P^{k1}_σ(K_m = k | H_m = h_m) > 0 → superSupp, {k | ∃ k1 ∈ K_i, 0 < P^{k1}_σ(H = h, K = k)}, indexed by the history alone; reason: the two conditions together say the joint probability is positive; the stage index is the history's length plus one
--   - encoding: K_{ℓn0+1} and P_{ℓn0+1} → stateAt (ℓ * n0) and belief after historyAt (ℓ * n0); reason: Lean stages count the recorded pairs from 0, so stage ℓn0 + 1 follows ℓ * n0 pairs
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Lemma 6.8, p.19

import Mathlib
import Definitions.Def_FiniteMemPOMDP_IsErgodic
import Definitions.Def_FiniteMemPOMDP_IsRepresentative
import Definitions.Def_FiniteMemPOMDP_blockStrategy

open MeasureTheory

namespace FiniteMemPOMDP

/-- **Lemma 6.8 — the block strategy tracks the super-support.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Lemma 6.8, p.19: "For all i ∈ [1 .. I], k ∈ Ki
and ℓ ≥ 0, we have that P^k_{σ′}(Kℓn0+1 ∈ D^{Jℓ}_i) = 1. Consequently,
D^{Jℓ} = (D^{Jℓ}_1, D^{Jℓ}_2, . . . , D^{Jℓ}_I) is a partition of the support of Pℓn0+1. Moreover,
P^{p∗}_{σ′}(Kℓn0+1 ∈ D^{Jℓ}_i) = p∗(Ki)."

Let `σ` be ergodic for `p∗`, `rep` a choice of representative histories, `n0 ≥ 1`, and `σ′` the
block strategy. Write `D_ℓ(ω)` for the super-support in force at stage `ℓ n0 + 1` of the play
`ω` (computed from the history `H_{ℓ n0 + 1}`). Then:
1. for every class value `c`, every `k ∈ K_c` and every `ℓ`, `P^k_{σ′}(K_{ℓn0+1} ∈ D_ℓ(c)) = 1`;
2. for every `ℓ`, `P^{p∗}_{σ′}`-almost surely the components `D_ℓ(c)` for distinct `c` are
   disjoint and their union is the support of the belief `P_{ℓn0+1}`;
3. for every `c` and `ℓ`, `P^{p∗}_{σ′}(K_{ℓn0+1} ∈ D_ℓ(c)) = p∗(K_c)`.

**Formalization Note** "partition of the support" is read as clause 2: disjoint components whose
union is the support; components may be empty (a nonempty-parts reading is false: two absorbing
states with distinct rewards and fully informative signals give `D_1 = ({x}, ∅)` with probability
`1/2`). Components are indexed by the class value `c ∈ ℝ` (empty for non-values). The lemma is
stated for every `n0 ≥ 1` (the paper uses the `n0` it has just chosen; the proof does not use the
choice). -/
theorem lemma_6_8 {K A S : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype S] [DecidableEq S] [Nonempty S]
    (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A) (hσ : IsErgodic Γ p σ)
    (rep : (ℝ → Set K) → List (A × S)) (hrep : IsRepresentative Γ p σ rep)
    (n0 : ℕ) (hn0 : 1 ≤ n0) :
    (∀ (c : ℝ), ∀ k ∈ valueClass Γ p σ c, ∀ ℓ : ℕ,
        (lawOfPlays Γ (pointBelief k) (blockStrategy Γ p σ rep n0)).real
          {ω | stateAt (ℓ * n0) ω ∈ blockTuple Γ p σ rep n0 (historyAt (ℓ * n0) ω) ℓ c} = 1) ∧
      (∀ ℓ : ℕ, ∀ᵐ ω ∂(lawOfPlays Γ p (blockStrategy Γ p σ rep n0)),
        (∀ c c' : ℝ, c ≠ c' →
          Disjoint (blockTuple Γ p σ rep n0 (historyAt (ℓ * n0) ω) ℓ c)
            (blockTuple Γ p σ rep n0 (historyAt (ℓ * n0) ω) ℓ c')) ∧
        (⋃ c : ℝ, blockTuple Γ p σ rep n0 (historyAt (ℓ * n0) ω) ℓ c) =
          {k | 0 < (belief Γ p (blockStrategy Γ p σ rep n0) (historyAt (ℓ * n0) ω)).1 k}) ∧
      ∀ (c : ℝ) (ℓ : ℕ),
        (lawOfPlays Γ p (blockStrategy Γ p σ rep n0)).real
            {ω | stateAt (ℓ * n0) ω ∈ blockTuple Γ p σ rep n0 (historyAt (ℓ * n0) ω) ℓ c} =
          ∑ k ∈ valueClass Γ p σ c, p.1 k := by sorry

end FiniteMemPOMDP
