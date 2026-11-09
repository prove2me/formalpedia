-- Prove2me | Theorems.Thm_DirTeleMC_schedule_arborescence
-- name    : DirTeleMC.schedule_arborescence
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:31:01.032691+00:00
-- url     : https://prove2.me/theorems/f2fe590d-aa65-43cb-80d5-1b1f803968dd
-- title:
--   §3, pp.8–9 — a valid schedule yields an out-arborescence of height and out-degree at most its length
-- statement:
--   Let $(G, s, K, k)$ be a well-formed instance, $S$ a valid schedule of length $T$, and $Y$ a nonempty set of vertices informed by $S$ (for instance the whole informed set, or the terminals it informs). Then there is an out-arborescence $A$ of $G$ rooted at $s$ such that:
--   1. $A$ contains $Y$ and all leaves of $A$ lie in $Y$;
--   2. every arc $(\mathrm{parent}(v), v)$ of $A$ is a call of $S$ in a round before which $v$ was not informed (a call that first informs $v$);
--   3. $A$ has height at most $T$ and every vertex has at most $T$ children;
--   4. $A$ has at most $1 + |Y|\cdot\mathrm{height}(A)$ vertices.
--
--   This is the bridge from schedules to trees: the comparison jump arborescence of the analysis is built from the arborescence of a short schedule.
--
--   Differences from the source:
--   - generalization: the arborescence of an optimal schedule → the arborescence of any valid schedule, with bounds in terms of its length; reason: an optimal schedule is a valid schedule of length OPT
--   - generalization: the arborescence of all informed vertices, and that arborescence pruned to the terminals → an arborescence of first-informing calls pruned to any nonempty set Y of informed vertices; reason: Y = the whole informed set gives the first sentence's arborescence, and Y = K (DTM) or the k informed terminals (k-multicast, p.31) gives the pruned one
--   - generalization: height and out-degree at most OPT → also at most 1 + |Y|·height vertices; reason: the vertex bound "at most 1 + kh*" of p.25 for the same tree; it adds a conclusion and drops nothing
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), §3 "Schedules and arborescences", pp.8–9 (PDF pp.9–10); vertex bound p.25 (PDF p.26)

import Mathlib
import Definitions.Def_DirTeleMC_Schedule
import Definitions.Def_DirTeleMC_Arb

namespace DirTeleMC

/-- **Schedules give out-arborescences** (§3 "Schedules and arborescences").
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), §3, pp.8–9: "From any feasible DTM schedule, retain one call that first informs each informed vertex
other than s. These calls form an out-arborescence: a directed tree rooted at s, with all arcs pointing away
from s." … "Second, the arborescence of an optimal schedule, pruned to the terminals, has height and maximum
out-degree at most OPT: calls along each root-to-terminal path occur in strictly increasing rounds, and each
vertex makes at most one call per round."

For every valid schedule `S` and every nonempty set `Y` of vertices informed by `S`, there is an
out-arborescence of `G` rooted at `s`, containing `Y`, with all leaves in `Y`, each of whose arcs is a call of
`S` that first informs its head, of height and maximum out-degree at most the length of `S`, and with at most
`1 + |Y| · height` vertices (the support bound used on p.31).

**Formalization Note.** The source states the bounds for an optimal schedule; they hold for every valid
schedule, which is what is stated. `Y` is any nonempty set of informed vertices: with `Y` the whole informed set
the tree is the arborescence of first-informing calls of the first sentence (its vertices are then exactly the
informed vertices); with `Y = K` (DTM) or the `k` informed terminals (k-multicast, p.31) it is the arborescence
pruned to the terminals of the second sentence. -/
theorem schedule_arborescence (I : Inst) (hI : I.WF) (S : Schedule I.n) (hS : S.Valid I)
    (Y : Finset (Fin I.n)) (hYne : Y.Nonempty)
    (hYinf : Y ⊆ informedAfter I.s S S.length) :
    ∃ A : Arb I.n, A.IsIn I.adj ∧ A.root = I.s ∧ Y ⊆ A.verts ∧ A.leaves ⊆ Y ∧
      (∀ v ∈ A.verts, v ≠ A.root → ∃ j, ∃ hj : j < S.length, (A.parent v, v) ∈ S[j] ∧
        v ∉ informedAfter I.s S j) ∧
      A.height ≤ S.length ∧ A.OutDegLE S.length ∧ A.verts.card ≤ 1 + Y.card * A.height := by sorry

end DirTeleMC
