-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_lemma_10_high_levels
-- name    : FakeUserRanking.FORC.lemma_10_high_levels
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-27T07:36:46.953205+00:00
-- url     : https://prove2.me/theorems/dacead8a-125a-4ee3-a8ae-09e1851f35f7
-- title:
--   Lemma 10 (Qualifying Levels): Pathwise Sub-Optimal Feedback Bound on G
-- statement:
--   **Qualifying-Level Pathwise Feedback Bound on $\mathcal G$ (Appendix D, pp. 57–59).** For all $n \ge 1$, $T \ge 2$, $F \ge 0$, every instance with click probabilities $\mu_1 > \dots > \mu_n$ in $[0,1]$, every resolution of FORC's tie-breaking and fallback rules, every trajectory $\tau \in \mathcal G$, every pair of products $j < i$, and every qualifying level $\ell = k + 1$ with $F \le 2^{k+1}$,
--
--   $$\sum_{t=1}^T \mathbf 1\big\{\ell_t = \ell \,\wedge\, A_{r,t}(\pi_t(j)=i)\big\} \le \gamma_{j,i} + 1,$$
--
--   where $\gamma_{j,i} = 64 \log(4nT/\delta) / \Delta_{j,i}^2$. By Lemma 15, on $\mathcal G$ the graph $G^{(\ell)}$ is a DAG of true comparisons, so whenever GraphRankSelect places product $i$ at position $j < i$, some product $m \le j$ remains unplaced with $(i, m) \notin G^{(\ell)}$ and $\eta^{(\ell)}_i \le \eta^{(\ell)}_m$, forcing $\eta^{(\ell)}_i < \gamma_{m,i} \le \gamma_{j,i}$.
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, Appendix D, pp. 57-59

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

open Classical in
/-- High-level pathwise feedback bound (Appendix D, pp. 57–59): on every trajectory in the good
event `G`, for every pair of products `j < i` and every qualifying level `k` (`F ≤ 2^(k+1)`),
the number of rounds where level `k` is sampled and `feedbackEvent` occurs for `(j, i)` is at
most `gamma T inst j i + 1`. -/
theorem lemma_10_high_levels (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (hG : goodEvent inst F tb fb τ)
    (j i : Fin n) (hji : j < i) (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) :
    (∑ t : Fin T, if (τ t).1 = k ∧ feedbackEvent (forc n T tb fb) τ t j i then (1 : ℝ) else 0) ≤
      gamma T inst j i + 1 := by sorry

end FakeUserRanking.FORC
