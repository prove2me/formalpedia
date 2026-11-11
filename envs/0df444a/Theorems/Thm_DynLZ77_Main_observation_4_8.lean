-- Prove2me | Theorems.Thm_DynLZ77_Main_observation_4_8
-- name    : DynLZ77.Main.observation_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:21:41.248625+00:00
-- url     : https://prove2.me/theorems/7aea0048-a1a7-4a4b-b6bc-23667bd88b6a
-- title:
--   Observation 4.8 — the root path of the LPF′-tree spells LZ77(S)
-- statement:
--   Let $\pi$ be the path from node $1$ to the root $n+1$ of the LPF′-tree $T_S$. The number of edges of $\pi$ is
--   $$|\pi|=\mathrm{depth}_S(1)=|\mathrm{LZ77}(S)|,$$
--   and for every $k\le|\pi|$, if the $k$-th edge of $\pi$ is $(i,i+\mathrm{LPF}'_S(i))$, then the $k$-th phrase of $\mathrm{LZ77}(S)$ is $S[i..i+\mathrm{LPF}'_S(i))$. In Lean, the $k$-th edge starts at `pathNode S (k-1)`, and the first clause says that the walk of $\mathrm{depth}_S(1)$ edges from $1$ ends at the root, i.e. it is $\pi$. This is the link that lets a dynamic tree on $T_S$ answer LZ77-queries.
--
--   Differences from the source:
--   - encoding: π, the path from 1 to the root, with |π| = depth_S(1) → pathNode S (depth S 1) = |S| + 1, and the k-th edge starts at pathNode S (k − 1); reason: states explicitly that the depth_S(1)-edge walk from 1 is the root path
--   - encoding: the kth phrase is equal to S[i..i + LPF′_S(i)) → the kth entry of LZ77 S is the position pair (i, i + LPF′_S(i) − 1); reason: phrases are kept with their positions, which is the paper's meaning of a phrase S[a..b]
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…), p. 18 (PDF 20), Observation 4.8

import Mathlib
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

/-- **Observation 4.8** (p. 18). The path `π` from node `1` to the root `n + 1` of the LPF′-tree
has `depth_S(1) = |LZ77(S)|` edges, and for `k ≤ |π|`, if the `k`-th edge of `π` is
`(i, i + LPF′_S(i))` then the `k`-th phrase of `LZ77(S)` is `S[i..i + LPF′_S(i))`. -/
theorem observation_4_8 {α : Type} [DecidableEq α] (S : List α) :
    pathNode S (depth S 1) = S.length + 1 ∧ depth S 1 = (LZ77 S).length ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ depth S 1 →
        (LZ77 S)[k - 1]? =
          some (pathNode S (k - 1), pathNode S (k - 1) + lpf' S (pathNode S (k - 1)) - 1) := by sorry

end DynLZ77.Main
