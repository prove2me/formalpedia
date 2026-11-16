-- Prove2me | Theorems.Thm_DetANN_HPIM_bisect_spec
-- name    : DetANN.HPIM.bisect_spec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-16T05:52:25.100553+00:00
-- url     : https://prove2.me/theorems/24a89532-7868-454f-ad22-6ec78db32583
-- title:
--   Binary search over a ladder by power-of-two steps
-- statement:
--   Let $Z_0,\dots,Z_{M-1}$ be box decision trees, read with the lookup clamped at the top (definition `DetANN_HPIMFormat`), and let $q\in\mathbb R^m$.
--
--   1. If the lookup at $lo$ is null and the lookup at $lo+2^t$ is not, then $hi=\mathrm{bisect}(t,lo)$ satisfies $hi\ge1$, the lookup at $hi-1$ is null and the lookup at $hi$ is not.
--   2. If every $Z_i$ visits at most $V$ nodes at $q$, the cost of $\mathrm{bisect}(t,lo)$ is at most $t(V+1)+1$.
--
--   In the tree of Har-Peled, Indyk and Motwani (2012, §2), the radii of the ladder grow geometrically and the lookups switch once from null to non-null. Item 1 finds the switch with $t=\lceil\log_2(M-1)\rceil$ probes. Since every step only adds a power of two, the search runs on a machine without division.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free.

import Mathlib
import Definitions.Def_DetANN_HPIMFormat

namespace DetANN.HPIM

/-- **The ladder search.** Let `Z_0, …, Z_{M−1}` be box decision trees and read the ladder clamped at
the top (`lookupC`). If the lookup at `lo` is null and the lookup at `lo + 2^t` is not, then
`hi = bisect Z q t lo` satisfies: the lookup at `hi − 1` is null, the lookup at `hi` is not, and
`hi ≥ 1`. If every lookup visits at most `V` nodes at `q`, the search costs at most `t (V + 1) + 1`. -/
theorem bisect_spec {m M : ℕ} (Z : Fin M → BoxTree m) (q : Fin m → ℝ) :
    (∀ t lo, lookupC Z lo q = none → lookupC Z (lo + 2 ^ t) q ≠ none →
      lookupC Z (bisect Z q t lo - 1) q = none ∧ lookupC Z (bisect Z q t lo) q ≠ none ∧
        1 ≤ bisect Z q t lo) ∧
    ∀ V : ℕ, (∀ i : Fin M, (Z i).visits q ≤ V) →
      ∀ t lo, bisectCost Z q t lo ≤ t * (V + 1) + 1 := by sorry

end DetANN.HPIM
