-- Prove2me | Theorems.Thm_DirTeleMC_lemma_3_1
-- name    : DirTeleMC.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:32:48.790898+00:00
-- url     : https://prove2.me/theorems/7d539f4d-976f-431f-9c67-56471fe35b49
-- title:
--   Lemma 3.1 — the busy schedule informs an arborescence within $h + |L| - 1$ rounds
-- statement:
--   **Lemma 3.1 (after Elkin and Kortsarz).** Let $Q$ be an out-arborescence rooted at an informed vertex, with height $h$ and leaf set $L$. In the busy schedule, each informed vertex calls one child it has not yet called in every round, until it has called all its children. Then every vertex of $Q$ is informed by round
--   $$h + |L| - 1,$$
--   and the schedule has at most $h + |L| - 1$ rounds.
--
--   Moreover, when $Q$ is an out-arborescence of $G$ rooted at $s$, the busy schedule is a valid schedule and informs every vertex of $Q$ in the round computed for it.
--
--   The lemma bounds the fallback schedule of Algorithm 2 (Lemma B.3).
--
--   Differences from the source:
--   - encoding: the busy schedule rooted at an informed vertex → the schedule along Q with an arbitrary child order, the root informed in round 0; reason: the page fixes no order in which a vertex calls its children; every order is covered
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Lemma 3.1, p.9 (PDF p.10); proof p.17 (PDF p.18)

import Mathlib
import Definitions.Def_DirTeleMC_Schedule
import Definitions.Def_DirTeleMC_arbSchedule

namespace DirTeleMC

/-- **Lemma 3.1** (busy schedule).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Lemma 3.1, p.9 (restated p.17): "Let Q be an out-arborescence rooted at an informed vertex, with height h
and leaf set L. In the busy schedule, each informed vertex calls one child it has not yet called in every
round, until it has called all its children. This schedule informs all vertices of Q within h + |L| − 1
rounds."

For every out-arborescence `Q` (a rooted tree on `Fin n`) and every order of the children of each vertex, in
the schedule along `Q` (the root informed in round `0`, and every vertex calling its children consecutively
from the round after it is informed) every vertex is informed by round `h + |L| − 1`, and the schedule has at
most `h + |L| − 1` rounds. When `Q` is an out-arborescence of `G` rooted at `s`, this schedule is a valid
schedule and informs every vertex of `Q` in the round `informTime` says.

**Formalization Note.** "The busy schedule" is the schedule along `Q` for an arbitrary child order (the order in
which a vertex calls its children is not fixed by the page). `|L| ≥ 1` always, so `h + |L| − 1` has no
truncation. -/
theorem lemma_3_1 (I : Inst) (Q : Arb I.n) (hQ : Q.IsTree) (ord : Fin I.n → List (Fin I.n))
    (hord : Q.IsChildOrder ord) :
    (∀ v ∈ Q.verts, Q.informTime ord v ≤ Q.height + Q.leaves.card - 1) ∧
      (Q.arbSchedule ord).length ≤ Q.height + Q.leaves.card - 1 ∧
      (Q.IsIn I.adj → Q.root = I.s →
        (Q.arbSchedule ord).Valid I ∧
          ∀ v ∈ Q.verts, v ∈ informedAfter I.s (Q.arbSchedule ord) (Q.informTime ord v)) := by sorry

end DirTeleMC
