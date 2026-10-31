-- Prove2me | Theorems.Thm_FiniteMemPOMDP_lemma_6_5
-- name    : FiniteMemPOMDP.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:47.466158+00:00
-- url     : https://prove2.me/theorems/e54bf256-b478-4b97-93f5-ba3e7ab04e35
-- title:
--   Lemma 6.5 (Continuation value)
-- statement:
--   Let $p^*\in\Delta(\mathcal K)$ and let $\sigma$ be ergodic for $p^*$, with value partition $\mathcal K_1,\dots,\mathcal K_I$ and class values $\gamma^1_\infty,\dots,\gamma^I_\infty$. For every stage $m\ge1$ and every class $i$, almost surely under $\mathbb P^{p^*}_\sigma$,
--
--   $$\forall k\in B^i_m:\qquad \gamma^k_\infty(\sigma_m)=\gamma^i_\infty,$$
--
--   where $B^i_m$ is the $i$-th component of the super-support at stage $m$ and $\sigma_m=\sigma[H_m]$ is the shifted strategy. Consequently the components $B^1_m,\dots,B^I_m$ are pairwise disjoint almost surely.
--
--   The Lean statement asserts both clauses for every history $h$ (not only almost surely).
--
--   Differences from the source:
--   - encoding: ∆(K), ∆(A) probability vectors; q: K × A → ∆(K × S); histories in ∪_m (A × S)^{m−1}; plays in (K × A × S)^ℕ; K, A, S finite → stdSimplex ℝ K / stdSimplex ℝ A; q as PMF (K × S); histories as chronological List (A × S); plays as ℕ → PlayStep A S K with coordinate n+1 = (A_{n+1}, S_{n+1}, K_{n+2}); K, A, S finite and nonempty; reason: Lean representations of the same objects; nonemptiness is implicit in the paper (p1 ∈ ∆(K), σ needs an action, q(k,a) ∈ ∆(K × S) needs a signal); the play space is a bijective re-indexing
--   - generalization: for all m ≥ 1, P^{p*}_σ-a.s. → for every history h (of every length); reason: a nonempty component B_c(h) forces P^{p*}_σ(H = h) > 0, so on null histories both clauses are trivial; the statement specializes to the almost-sure one
--   - encoding: classes i ∈ [1 .. I] with values γ^i_∞ → classes indexed by their value c ∈ ℝ (empty for non-values); reason: the class of value c is K_i for c = γ^i_∞; empty classes give empty components and trivial clauses
--   - encoding: B^i_m(h_m) defined by P^{k1}_σ(H_m = h_m) > 0 and P^{k1}_σ(K_m = k | H_m = h_m) > 0 → superSupp, {k | ∃ k1 ∈ K_i, 0 < P^{k1}_σ(H = h, K = k)}, indexed by the history alone; reason: the two conditions together say the joint probability is positive; the stage index is the history's length plus one
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Lemma 6.5, p.17

import Mathlib
import Definitions.Def_FiniteMemPOMDP_IsErgodic
import Definitions.Def_FiniteMemPOMDP_superSupp
import Definitions.Def_FiniteMemPOMDP_shift

namespace FiniteMemPOMDP

/-- **Lemma 6.5 (Continuation value).**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Lemma 6.5, p.17: "For all m ≥ 1 and
i ∈ [1 .. I] it holds P^{p∗}_σ-a.s. that ∀k ∈ B^i_m  γ^k_∞(σm) = γ^i_∞. Consequently,
B^1_m, . . . , B^I_m are disjoint P^{p∗}_σ-a.s." Standing assumption of §6 (p.14): "fix
p∗ ∈ ∆(K), which will be used as an initial belief, and σ an ergodic strategy for p∗."

Let `σ` be ergodic for `p∗`. For every history `h` and every class value `c`, every state `k` in
the component `B_c(h)` of the super-support after `h` satisfies `γ^k_∞(σ[h]) = c`; and the
components belonging to different class values are disjoint.

**Formalization Note** The paper's "`P^{p∗}_σ`-a.s." is stated for every history `h`: a
nonempty component `B_c(h)` forces `P^{p∗}_σ(H = h) > 0`, so on histories of probability zero
both clauses are trivial. The value classes are indexed by their value `c ∈ ℝ` (see
`valueClass`). -/
theorem lemma_6_5 {K A S : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype S] [DecidableEq S] [Nonempty S]
    (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A) (hσ : IsErgodic Γ p σ) :
    (∀ (h : List (A × S)) (c : ℝ), ∀ k ∈ superSuppTuple Γ p σ h c,
        gammaInf Γ (pointBelief k) (shift σ h) = c) ∧
      ∀ (h : List (A × S)) (c c' : ℝ), c ≠ c' →
        Disjoint (superSuppTuple Γ p σ h c) (superSuppTuple Γ p σ h c') := by sorry

end FiniteMemPOMDP
