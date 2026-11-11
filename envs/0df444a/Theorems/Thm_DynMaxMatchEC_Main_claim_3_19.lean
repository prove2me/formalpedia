-- Prove2me | Theorems.Thm_DynMaxMatchEC_Main_claim_3_19
-- name    : DynMaxMatchEC.Main.claim_3_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:03:58.322229+00:00
-- url     : https://prove2.me/theorems/4bfe13ae-394e-4c1d-939e-9e74cb39363c
-- title:
--   Claim 3.19 — one call of the randomized ProcAugment fails with probability at most 1/2
-- statement:
--   Let $M_1,\dots,M_{z'}$ and $M^*$ be matchings of a graph $G$ on $n$ vertices, $z\ge1$, $\hat x\ge1$ an integer and $i^*$ an index such that at most $12n\hat x/z$ vertices of $S\cup\bar A$ are unmatched in $M_{i^*}$. Let $\tilde{\mathcal E}$ be the event that ProcAugment (Figure 6) with index $i^*$ terminates with FAIL: Step 1 returns when $|S'|+|\bar A'|\le32n\hat x/z$; otherwise a vertex $v\in S'\cup\bar A'$ is chosen uniformly and the call fails if $P_{i^*}(v)$ is long, has no edge, is terrible or is bad. Then
--   $$\Pr[\tilde{\mathcal E}]\le\frac12 .$$
--
--   Differences from the source:
--   - generalization: a call made by the algorithm of §3.3, with i∗ retrieved from D′_A → any matchings M_i, M∗ of G and any index i∗ with n_{i∗} = #{v ∈ S ∪ Ā unmatched in M_{i∗}} ≤ 12nx̂/z; reason: this is the only property of the state the proof uses
--   - generalization: x̂ = x^{3/2} → any integer x̂ ≥ 1; reason: the proof uses only x̂ ≥ 1
--   - encoding: Pr[Ẽ] over v uniform in S′ ∪ Ā′ → the exact uniform-counting probability augmentFailProb with threshold 32nx̂/z, 0 when Step 1 returns; reason: the procedure's only randomness is this choice
--   - encoding: I = {1, …, z′} → Fin z′; reason: 0-based indices
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 38, Claim 3.19 (Figure 6, p. 39; setting pp. 25–30)

import Mathlib
import Definitions.Def_DynMaxMatchEC_Main_Model
import Definitions.Def_DynMaxMatchEC_Main_PathState

open Classical

namespace DynMaxMatchEC.Main

/-- **Claim 3.19** (Chuzhoy, manuscript Nov. 1, 2026, PDF sha256 2c277528…4ca5, p. 38). Let
`M_1, …, M_{z'}` and `M∗` be matchings of `G`, `z ≥ 1`, `x̂ ≥ 1` an integer, and `i∗` an index such
that at most `12nx̂/z` vertices of `S ∪ Ā` are unmatched in `M_{i∗}`. Then the probability that
`ProcAugment` (Figure 6, with index `i∗` and Step 1 threshold `32nx̂/z`) ends with FAIL is at most
`1/2`. -/
theorem claim_3_19 (n z' z : ℕ) (σ : MState n z')
    (hcolG : ∀ i, ∀ e ∈ σ.col i, e ∈ σ.G.edgeSet) (hstarG : ∀ e ∈ σ.Mstar, e ∈ σ.G.edgeSet)
    (hcol : ∀ i, IsMatching (σ.col i)) (hstar : IsMatching σ.Mstar)
    (hz : 1 ≤ z) (xhat : ℕ) (hxhat : 1 ≤ xhat) (istar : Fin z')
    (hni : (((σ.S ∪ σ.Abar).filter fun v => ¬ IsMatchedIn (σ.col istar) v).card : ℝ) ≤
      12 * n * xhat / z) :
    σ.augmentFailProb z istar (32 * n * xhat / z) ≤ 1 / 2 := by sorry

end DynMaxMatchEC.Main
