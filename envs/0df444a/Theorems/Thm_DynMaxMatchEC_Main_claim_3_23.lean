-- Prove2me | Theorems.Thm_DynMaxMatchEC_Main_claim_3_23
-- name    : DynMaxMatchEC.Main.claim_3_23
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:03:38.582694+00:00
-- url     : https://prove2.me/theorems/41383280-8fa3-4187-90da-503eb6834035
-- title:
--   Claim 3.23 — fewer than 64ρxn/x̂ vertices of Λ̂(v) are matched in M∗ with J(u) = ∅
-- statement:
--   Consider a state of the deterministic matching algorithm satisfying the hypotheses of Claim 3.13, with $x\ge1$ and an integer $1\le\hat x\le xn$, in which $\hat\Lambda(v)\subseteq N_G(v)\cap(A\cup\hat T)$, $|\hat T|\le\rho$, and every $u\in A$ has $m(u)\le z-2\hat x$ and $|I(u)|=\hat x$, every $I(u)$ consisting of indices at which $u$ is unmatched. Let $J(u)$ be the set of indices $i$ for which $P_i(u)$ is defined, short, not terrible and has at least one edge. Then
--   $$\#\{u\in\hat\Lambda(v): u\text{ matched in }M^*,\ J(u)=\emptyset\}<\frac{64\rho xn}{\hat x}.$$
--   So among the first $\lceil64\rho xn/\hat x\rceil$ vertices of $\hat\Lambda(v)$ there is one that is unmatched or has $J(u)\ne\emptyset$, which makes the derandomized ProcSettleS never fail.
--
--   Differences from the source:
--   - generalization: a call made by the algorithm of §3.3 on its current state → any state satisfying the hypotheses listed (those of Claim 3.13, Λ̂(v) ⊆ N(v) ∩ (A ∪ T̂), |T̂| ≤ ρ, m(u) ≤ z − 2x̂ and |I(u)| = x̂ for u ∈ A, I(u) ⊆ indices where u is unmatched); reason: these are the invariants the proof uses; every state of the algorithm satisfies them
--   - generalization: x̂ = x^{3/2} and ρ = c log n → any integer x̂ with 1 ≤ x̂ ≤ x·n, any integer x ≥ 1 and any real ρ ≥ 1; reason: the proof uses only x̂ ≤ xn, |I(u)| = x̂, x ≥ 1 and ρ ≥ 1; x^{3/2} need not be an integer, and the paper uses x̂ as one
--   - reading: J(u), maintained by the deterministic algorithm's data structure (pp. 31–32) → the set J(u) as defined on p. 31 (indices i with P_i(u) defined, short, not terrible, with an edge), computed from the state; reason: the claim's proof uses exactly this semantic set; the maintained set can differ from it after block ends (INSIGHTS.yaml I1)
--   - encoding: I = {1, …, z′} → Fin (z + x); reason: 0-based indices
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 43, Claim 3.23 (J(v) defined p. 31; setting pp. 25–32)

import Mathlib
import Definitions.Def_DynMaxMatchEC_Main_Model
import Definitions.Def_DynMaxMatchEC_Main_PathState

open Classical

namespace DynMaxMatchEC.Main

/-- **Claim 3.23** (Chuzhoy, manuscript Nov. 1, 2026, PDF sha256 2c277528…4ca5, p. 43). Under the
hypotheses of Claim 3.13, let `x ≥ 1`, let `x̂` be an integer with `1 ≤ x̂ ≤ xn`, let
`Λ̂(v) ⊆ N_G(v) ∩ (A ∪ T̂)` with `|T̂| ≤ ρ`, and for `u ∈ A` let `m(u) ≤ z − 2x̂` and `|I(u)| = x̂`,
every `I(u)` consisting of indices at which `u` is unmatched. Then fewer than `64ρxn/x̂` vertices
`u ∈ Λ̂(v)` are matched in `M∗` and have `J(u) = ∅`, where `J(u)` is the set of indices `i` with
`P_i(u)` defined, short, not terrible and with at least one edge. -/
theorem claim_3_23 (n z x : ℕ) (σ : MState n (z + x)) (ρ : ℝ)
    (hcolG : ∀ i, ∀ e ∈ σ.col i, e ∈ σ.G.edgeSet) (hstarG : ∀ e ∈ σ.Mstar, e ∈ σ.G.edgeSet)
    (hcol : ∀ i, IsMatching (σ.col i)) (hdisj : ∀ i j, i ≠ j → Disjoint (σ.col i) (σ.col j))
    (hstar : IsMatching σ.Mstar) (hxz : x ≤ z) (hρ : 1 ≤ ρ)
    (hP1 : ∀ v, mdeg σ.Mall v ≤ z)
    (hS : ∀ v ∈ σ.S, (z : ℝ) - (ρ - 1) * x ≤ mdeg σ.Mall v)
    (hx : 1 ≤ x) (xhat : ℕ) (hxhat : 1 ≤ xhat) (hxhatn : xhat ≤ x * n) (v : Fin n)
    (hL : σ.Lhat v ⊆ Finset.univ.filter fun u => σ.G.Adj v u ∧ (u ∈ σ.A ∨ u ∈ σ.That))
    (hThat : (σ.That.card : ℝ) ≤ ρ)
    (hA : ∀ u ∈ σ.A, (mdeg σ.Mall u : ℝ) ≤ z - 2 * xhat)
    (hI : ∀ u, σ.Iset u ⊆ Finset.univ.filter fun i => ¬ IsMatchedIn (σ.col i) u)
    (hIA : ∀ u ∈ σ.A, (σ.Iset u).card = xhat) :
    (((σ.Lhat v).filter fun u => IsMatchedIn σ.Mstar u ∧ σ.J z u = ∅).card : ℝ) <
      64 * ρ * x * n / xhat := by sorry

end DynMaxMatchEC.Main
