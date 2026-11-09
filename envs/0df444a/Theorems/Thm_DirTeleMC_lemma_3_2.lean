-- Prove2me | Theorems.Thm_DirTeleMC_lemma_3_2
-- name    : DirTeleMC.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:33:16.068065+00:00
-- url     : https://prove2.me/theorems/8fe866a1-e2b2-4040-9ee7-381e277a0005
-- title:
--   Lemma 3.2 — leaf-ordered schedules finish within $h + d\log|L|/\log d$ rounds
-- statement:
--   **Lemma 3.2 (after Ravi).** Let $T$ be an out-arborescence rooted at an informed vertex, with height $h$, leaf set $L$ and every out-degree at most $d \ge 2$.
--   1. If each vertex calls its children in non-increasing order of the number of leaves in their subtrees, every vertex of $T$ is informed by round
--   $$h + \frac{d \log |L|}{\log d}.$$
--   2. If the children are ordered by non-increasing subtree size, every vertex is informed by round $h + d\log|V(T)|/\log d$.
--
--   The lemma turns a shallow, low-degree tree into a short schedule; Lemma B.2 applies it to the trees built by SCHEDULE.
--
--   **Formalization Note** The root is informed in round $0$; the leaf set of a finite tree is never empty.
--
--   Differences from the source:
--   - generalization: maximum out-degree at most d ≥ 2 → d any real number ≥ 2; reason: integer d is a special case; Lemma B.2 applies the lemma with the real d = max{Λ(J), k^{1/ℓ}, 2}
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Lemma 3.2, p.9 (PDF p.10); proof pp.17–18 (PDF pp.18–19)

import Mathlib
import Definitions.Def_DirTeleMC_arbSchedule

namespace DirTeleMC

/-- **Lemma 3.2** (leaf-ordered schedule).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Lemma 3.2, p.9 (restated p.17): "Let T be an out-arborescence rooted at an informed vertex, with height h,
nonempty leaf set L, and maximum out-degree at most d ≥ 2. If each vertex calls its children in non-increasing
order of the number of leaves in their subtrees, all vertices of T are informed within h + d log |L|/ log d
rounds. The same bound holds with |V(T)| in place of |L| when children are ordered by non-increasing subtree
size."

For every rooted tree `T` with every out-degree at most a real `d ≥ 2`: (1) if every child order is
non-increasing in the leaf counts of the children's subtrees, every vertex is informed by round
`h + d log |L| / log d`; (2) if it is non-increasing in subtree sizes, by round `h + d log |V(T)| / log d`.

**Formalization Note.** The root is informed in round `0`. `Real.log` is the natural logarithm; the ratio of
logarithms does not depend on the base. The leaf set of a finite tree is never empty. `d` is real, which covers
every integer `d ≥ 2` and the real `d` of Lemma B.2. -/
theorem lemma_3_2 {n : ℕ} (T : Arb n) (hT : T.IsTree) (ord : Fin n → List (Fin n))
    (hord : T.IsChildOrder ord) (d : ℝ) (hd : 2 ≤ d)
    (hdeg : ∀ u ∈ T.verts, ((T.children u).card : ℝ) ≤ d) :
    ((∀ u ∈ T.verts, (ord u).Pairwise fun a b => T.leafCount b ≤ T.leafCount a) →
      ∀ v ∈ T.verts,
        (T.informTime ord v : ℝ) ≤ T.height + d * Real.log T.leaves.card / Real.log d) ∧
    ((∀ u ∈ T.verts, (ord u).Pairwise fun a b => T.subtreeSize b ≤ T.subtreeSize a) →
      ∀ v ∈ T.verts,
        (T.informTime ord v : ℝ) ≤ T.height + d * Real.log T.verts.card / Real.log d) := by sorry

end DirTeleMC
