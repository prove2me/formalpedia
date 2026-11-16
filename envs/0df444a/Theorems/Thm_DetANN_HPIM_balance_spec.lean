-- Prove2me | Theorems.Thm_DetANN_HPIM_balance_spec
-- name    : DetANN.HPIM.balance_spec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-16T05:52:33.818587+00:00
-- url     : https://prove2.me/theorems/5dad404d-3b67-48c3-82f1-c2f5745397ab
-- title:
--   Centroid balancing of a BSP is correct and has logarithmic depth
-- statement:
--   Let $T$ be a BSP in $\mathbb R^m$ that covers (definition `DetANN_HPIMBSP`), with $|T|$ nodes, and let $B$ be its balancing with fuel $|T|+1$ from the root. For every $q\in\mathbb R^m$:
--
--   1. if $q$ lies in the root box, then $B(q)$ is the answer of some leaf of $T$ whose box contains $q$;
--   2. $B$ visits at most $5\lfloor\log_2|T|\rfloor+6$ nodes at $q$.
--
--   The depth of $T$ itself can be linear in $|T|$; balancing makes the query cost logarithmic in its size. In the floor-free proof of `DetANN.lemma_3_3`, every near-neighbour lookup is a certified BSP whose leaves are correct answers, so this turns each lookup into a box decision tree with $O(\log|T|)$ visits.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free. The balancing is the standard centroid decomposition of a tree.

import Mathlib
import Definitions.Def_DetANN_HPIMBSP

namespace DetANN.HPIM

/-- **Centroid balancing of a BSP.** Let `T` be a BSP in `ℝ^m` whose cuts cover their boxes, with
`|T|` nodes. The balanced box decision tree `balance T (|T| + 1) [] ∅` answers, at every `q` in the
root box, the answer of a leaf of `T` whose box contains `q`, and it visits at most
`5 ⌊log₂ |T|⌋ + 6` nodes at every `q`. -/
theorem balance_spec {m : ℕ} (T : BSP m) (hT : T.Covers) (q : Fin m → ℝ) :
    (InBox T.box.1 T.box.2 q → ∃ p lo hi a, T.sub p = some (.leaf lo hi a) ∧ InBox lo hi q ∧
      (balance T (T.paths.card + 1) [] ∅).eval q = a) ∧
    (balance T (T.paths.card + 1) [] ∅).visits q ≤ 5 * Nat.log 2 T.paths.card + 6 := by sorry

end DetANN.HPIM
