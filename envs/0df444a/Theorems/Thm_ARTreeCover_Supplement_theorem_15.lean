-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_15
-- name    : ARTreeCover.Supplement.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:05:15.941827+00:00
-- url     : https://prove2.me/theorems/b840a460-eec0-4e4e-8ad4-6fb09ec5ecf7
-- title:
--   Theorem 15 — $K_r$-minor-free graphs have weak $(\Delta,O(k))$-padded decompositions with probability $r^{-O(1/k)}$
-- statement:
--   There is an absolute constant $C>0$ such that for every real $k\ge1$, every integer $r\ge2$ and every $\Delta>0$, every weighted $K_r$-minor-free graph $G$ admits a weak $(\Delta,Ck)$-padded decomposition with probability parameter
--   $$p=r^{-C/k}.$$
--
--   That is, there is a probability distribution over partitions of $V$ whose clusters have weak radius at most $Ck\Delta$, such that for every vertex $u$ the ball $B_G(u,\Delta)$ lies inside one cluster with probability at least $r^{-C/k}$. With Lemma 2 this gives Theorem 14.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - generalization: k ≥ 1 (type not stated; k is an integer in the neighbouring theorems) → k a real number with k ≥ 1; reason: every integer k ≥ 1 is a real k ≥ 1, so the statement specializes to the integer reading
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 15, p.17 (PDF p.20)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_IsProbabilisticDecomp
import Definitions.Def_ARTreeCover_Supplement_KrMinorFree

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 15**, p.17 (PDF p.20). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"For any k ≥ 1, r = 2, 3, . . . and ∆ > 0, every undirected weighted Kr-minor-free graph admits a
weak (∆, O(k))-padded decomposition with probability parameter r^{−O(1/k)}."

**Formalization Note.**
1. One absolute `C > 0` (chosen before `V`, `G`, `k`, `r`, `∆`) serves both O(·): radius blow-up
   `C · k` and probability parameter `r^{−C/k}` (a larger `C` weakens both, so one constant is
   the same as two).
2. `k ≥ 1` is real (the printed statement leaves its type open; real is the more general reading).
3. The decomposition is the published `IsPaddedDecomp` with `strong = false` (weak radius), a `PMF`
   on partitions of `V`. -/
theorem theorem_15 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (k Δ : ℝ) (r : ℕ),
        1 ≤ k → 2 ≤ r → 0 < Δ → KrMinorFree r G →
        ∃ D : PMF (Finpartition (Finset.univ : Finset V)),
          IsPaddedDecomp G false Δ (C * k) ((r : ℝ) ^ (-(C / k))) D := by sorry

end ARTreeCover.Supplement
