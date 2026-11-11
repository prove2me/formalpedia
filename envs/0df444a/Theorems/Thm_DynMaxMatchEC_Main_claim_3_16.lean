-- Prove2me | Theorems.Thm_DynMaxMatchEC_Main_claim_3_16
-- name    : DynMaxMatchEC.Main.claim_3_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:03:16.531014+00:00
-- url     : https://prove2.me/theorems/0f6341d5-c197-4365-83ed-62277e656269
-- title:
--   Claim 3.16 — one call of the randomized ProcSettleS(v) fails with probability at most 1/4
-- statement:
--   Consider a state of the randomized matching algorithm satisfying the hypotheses of Claim 3.13, with $x\ge1$, an integer $1\le\hat x\le xn$ and $r=\lceil64\rho xn/\hat x\rceil$, in which $\hat\Lambda(v)\subseteq N_G(v)\cap(A\cup\hat T)$, $|\hat T|\le\rho$, every $u\in A$ has $m(u)\le z-2\hat x$ and $|I(u)|=\hat x$, every $I(u)$ consists of indices at which $u$ is unmatched, and the first $r$ entries of $\hat\Lambda(v)$ are $r$ of its vertices when $|\hat\Lambda(v)|>r$. Then for every $v\in S'$ the event $\mathcal E_v$ that ProcSettleS$(v)$ (Figure 5) terminates with FAIL satisfies
--   $$\Pr[\mathcal E_v]\le\frac14 .$$
--
--   Differences from the source:
--   - generalization: a call made by the algorithm of §3.3 on its current state → any state satisfying the hypotheses listed (those of Claim 3.13, Λ̂(v) ⊆ N(v) ∩ (A ∪ T̂), |T̂| ≤ ρ, m(u) ≤ z − 2x̂ and |I(u)| = x̂ for u ∈ A, I(u) ⊆ indices where u is unmatched); reason: these are the invariants the proof uses; every state of the algorithm satisfies them
--   - generalization: x̂ = x^{3/2} and ρ = c log n → any integer x̂ with 1 ≤ x̂ ≤ x·n, any integer x ≥ 1 and any real ρ ≥ 1; reason: the proof uses only x̂ ≤ xn, |I(u)| = x̂, x ≥ 1 and ρ ≥ 1; x^{3/2} need not be an integer, and the paper uses x̂ as one
--   - encoding: Pr[E_v], over the procedure's random choices (u uniform among the first ⌈64ρxn/x̂⌉ vertices of Λ̂(v), i uniform in I(u)) → the exact uniform-counting probability settleSFailProb, 0 when Step 2 or Step 3 terminates; reason: the procedure's randomness is exactly these two uniform choices
--   - encoding: Step 6 selects i ∈ I(u) uniformly → if I(u) were empty the call is counted as failing; reason: Step 6 cannot run then; counting it as failure can only increase the probability
--   - encoding: the first ⌈64ρxn/x̂⌉ vertices of Λ̂(v), I = {1, …, z′} → a given subset of Λ̂(v) of that size (the extended search structure's U′); Fin (z + x); reason: the structure keeps an arbitrary such subset; 0-based indices
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 37, Claim 3.16 (Figure 5, p. 36; setting pp. 25–35)

import Mathlib
import Definitions.Def_DynMaxMatchEC_Main_Model
import Definitions.Def_DynMaxMatchEC_Main_PathState

open Classical

namespace DynMaxMatchEC.Main

/-- **Claim 3.16** (Chuzhoy, manuscript Nov. 1, 2026, PDF sha256 2c277528…4ca5, p. 37). Under the
hypotheses of Claim 3.13, let `x ≥ 1`, let `x̂` be an integer with `1 ≤ x̂ ≤ xn` and
`r = ⌈64ρxn/x̂⌉`; let `Λ̂(v) ⊆ N_G(v) ∩ (A ∪ T̂)` with `|T̂| ≤ ρ`; for `u ∈ A` let `m(u) ≤ z − 2x̂`
and `|I(u)| = x̂`; let every `I(u)` consist of indices at which `u` is unmatched; and let the first
`r` entries of `Λ̂(v)` be `r` of its vertices when `|Λ̂(v)| > r`. Then for every `v ∈ S′` the
probability that `ProcSettleS(v)` (Figure 5) ends with FAIL is at most `1/4`. -/
theorem claim_3_16 (n z x : ℕ) (σ : MState n (z + x)) (ρ : ℝ)
    (hcolG : ∀ i, ∀ e ∈ σ.col i, e ∈ σ.G.edgeSet) (hstarG : ∀ e ∈ σ.Mstar, e ∈ σ.G.edgeSet)
    (hcol : ∀ i, IsMatching (σ.col i)) (hdisj : ∀ i j, i ≠ j → Disjoint (σ.col i) (σ.col j))
    (hstar : IsMatching σ.Mstar) (hxz : x ≤ z) (hρ : 1 ≤ ρ)
    (hP1 : ∀ v, mdeg σ.Mall v ≤ z)
    (hS : ∀ v ∈ σ.S, (z : ℝ) - (ρ - 1) * x ≤ mdeg σ.Mall v)
    (hx : 1 ≤ x) (xhat : ℕ) (hxhat : 1 ≤ xhat) (hxhatn : xhat ≤ x * n)
    (v : Fin n) (hv : v ∈ σ.S')
    (hL : σ.Lhat v ⊆ Finset.univ.filter fun u => σ.G.Adj v u ∧ (u ∈ σ.A ∨ u ∈ σ.That))
    (hThat : (σ.That.card : ℝ) ≤ ρ)
    (hA : ∀ u ∈ σ.A, (mdeg σ.Mall u : ℝ) ≤ z - 2 * xhat)
    (hI : ∀ u, σ.Iset u ⊆ Finset.univ.filter fun i => ¬ IsMatchedIn (σ.col i) u)
    (hIA : ∀ u ∈ σ.A, (σ.Iset u).card = xhat)
    (hfirst : σ.Lfirst v ⊆ σ.Lhat v)
    (hfirstcard : ⌈64 * ρ * x * n / xhat⌉₊ < (σ.Lhat v).card →
      (σ.Lfirst v).card = ⌈64 * ρ * x * n / xhat⌉₊) :
    σ.settleSFailProb z ⌈64 * ρ * x * n / xhat⌉₊ v ≤ 1 / 4 := by sorry

end DynMaxMatchEC.Main
