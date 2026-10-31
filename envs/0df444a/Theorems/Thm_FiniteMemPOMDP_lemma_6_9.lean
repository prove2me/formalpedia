-- Prove2me | Theorems.Thm_FiniteMemPOMDP_lemma_6_9
-- name    : FiniteMemPOMDP.lemma_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:35:20.80359+00:00
-- url     : https://prove2.me/theorems/8e114e65-8e93-4420-9b1d-ae39b913876a
-- title:
--   Lemma 6.9 — block averages of $\sigma'$ are at least $\gamma^{p^*}_\infty(\sigma)-\varepsilon$
-- statement:
--   Let $p^*\in\Delta(\mathcal K)$, let $\sigma$ be ergodic for $p^*$, let $\varepsilon>0$, let $n_0$ be a block length chosen as in §6.4, and let $\sigma'$ be the block strategy. For every $L\in\mathbb N^*$,
--
--   $$\mathbb E^{p^*}_{\sigma'}\Big(\frac1{Ln_0}\sum_{m=1}^{Ln_0}G_m\Big)\ge\gamma^{p^*}_\infty(\sigma)-\varepsilon .$$
--
--   Differences from the source:
--   - encoding: ∆(K), ∆(A) probability vectors; q: K × A → ∆(K × S); histories in ∪_m (A × S)^{m−1}; plays in (K × A × S)^ℕ; K, A, S finite → stdSimplex ℝ K / stdSimplex ℝ A; q as PMF (K × S); histories as chronological List (A × S); plays as ℕ → PlayStep A S K with coordinate n+1 = (A_{n+1}, S_{n+1}, K_{n+2}); K, A, S finite and nonempty; reason: Lean representations of the same objects; nonemptiness is implicit in the paper (p1 ∈ ∆(K), σ needs an action, q(k,a) ∈ ∆(K × S) needs a signal); the play space is a bijective re-indexing
--   - encoding: n0 chosen in §6.4 for ε; J_ℓ, h^j → hypothesis GoodBlockLength Γ p σ rep ε n0; rep with IsRepresentative; reason: GoodBlockLength is the §6.4 property of n0 verbatim; the paper's choice of h^j is arbitrary
--   - encoding: B^i_m(h_m) defined by P^{k1}_σ(H_m = h_m) > 0 and P^{k1}_σ(K_m = k | H_m = h_m) > 0 → superSupp, {k | ∃ k1 ∈ K_i, 0 < P^{k1}_σ(H = h, K = k)}, indexed by the history alone; reason: the two conditions together say the joint probability is positive; the stage index is the history's length plus one
--   - encoding: classes i ∈ [1 .. I] with values γ^i_∞ in the property of n0 → class values c ∈ ℝ in GoodBlockLength; reason: the class of value c is K_i for c = γ^i_∞; empty components for non-values make those clauses vacuous
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Lemma 6.9, p.20

import Mathlib
import Definitions.Def_FiniteMemPOMDP_IsErgodic
import Definitions.Def_FiniteMemPOMDP_IsRepresentative
import Definitions.Def_FiniteMemPOMDP_GoodBlockLength
import Definitions.Def_FiniteMemPOMDP_blockStrategy

open MeasureTheory

namespace FiniteMemPOMDP

/-- **Lemma 6.9 — the block strategy guarantees `γ^{p∗}_∞(σ) − ε` on every multiple of `n0`.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Lemma 6.9, p.20: "Let L ∈ N∗. The following
inequality holds: E^{p∗}_{σ′} ( (1/(Ln0)) ∑_{m=1}^{Ln0} Gm ) ≥ γ^{p∗}_∞(σ) − ε."

Let `σ` be ergodic for `p∗`, `rep` a choice of representative histories, `ε > 0`, and `n0` a
block length chosen as in §6.4 (`GoodBlockLength`). Then for every `L ≥ 1` the block strategy
`σ′` satisfies `E^{p∗}_{σ′}((1/(L n0)) ∑_{m=1}^{L n0} G_m) ≥ γ^{p∗}_∞(σ) − ε`. -/
theorem lemma_6_9 {K A S : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype S] [DecidableEq S] [Nonempty S]
    (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A) (hσ : IsErgodic Γ p σ)
    (rep : (ℝ → Set K) → List (A × S)) (hrep : IsRepresentative Γ p σ rep)
    (ε : ℝ) (hε : 0 < ε) (n0 : ℕ) (hn0 : GoodBlockLength Γ p σ rep ε n0) (L : ℕ) (hL : 1 ≤ L) :
    gammaInf Γ p σ - ε ≤
      ∫ ω, avgReward Γ (L * n0) ω ∂(lawOfPlays Γ p (blockStrategy Γ p σ rep n0)) := by sorry

end FiniteMemPOMDP
