-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_lemma_5_9
-- name    : ConstrainedDirSep.STSep.lemma_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:08:45.92792+00:00
-- url     : https://prove2.me/theorems/3644b32b-e903-4881-b80f-093b443a4a42
-- title:
--   Lemma 5.9 — an assignment satisfies every splicing constraint iff its selected split arcs form an s–t cut, then a minimum one
-- statement:
--   Let $H$ be a finite capacity-one directed multigraph with distinct terminals $s,t$, let $P_1,\dots,P_\lambda$ be pairwise arc-disjoint directed $s$–$t$ paths forming a maximum flow (some $s$–$t$ cut has exactly $\lambda$ arcs), and fix a set of split arcs such that every $P_i$ carries $d_i\ge1$ of them. For an assignment $x$ with $x_i\in[d_i]$,
--   $$x \text{ satisfies every splicing constraint (10)} \iff Z(x)=\{c_i(x_i): i\in[\lambda]\}\text{ is an } s\text{–}t \text{ cut in } H,$$
--   and every such cut is a minimum cut: it has no more arcs than any $s$–$t$ cut of $H$.
--
--   This describes all minimum cuts of a flow-augmentation branch by ordered variables and local constraints, the basis of the ordered representations of Theorem 5.2.
--
--   Differences from the source:
--   - generalization: H the parallel expansion of G + A for the split graph G of D, the flow paths of its maximum flow, and the split arcs e_v → any finite capacity-one multigraph H, any λ arc-disjoint s–t paths forming a maximum flow, and any set of designated arcs with at least one on each path; reason: the proof uses only these properties, and the source's branch is an instance.
--   - encoding: paths as vertex/arc sequences → arc lists with consecutive arcs joined and no repeated vertex; connectors of type (i) as a first off-flow arc followed by a walk through off-flow vertices; reason: a walk with these properties shortens to a path, so existence is unchanged.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 22 (PDF 25), Lemma 5.9 (proof pp. 22–23, PDF 25–26)

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Multigraph
import Definitions.Def_ConstrainedDirSep_STSep_Splicing

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 22 (PDF 25), Lemma 5.9: for flow paths `P_1, …, P_λ` forming a maximum
flow of the capacity-one multigraph `H`, each carrying at least one split arc, an assignment
`x ∈ [d_1] × ⋯ × [d_λ]` satisfies every splicing constraint (10) iff
`Z(x) = {c_i(x_i) : i ∈ [λ]}` is an s–t cut of `H`; every such cut is a minimum cut. -/
theorem lemma_5_9 {V A : Type*} [Finite A] (Φ : FlowFrame V A) (hst : Φ.s ≠ Φ.t)
    (hP : Φ.IsArcDisjointPaths)
    (hmax : ∃ Z : Set A, Φ.H.IsArcCut Φ.s Φ.t Z ∧ Z.ncard = Φ.lam)
    (hd : ∀ i, 1 ≤ Φ.dom i)
    (x : Fin Φ.lam → ℕ) (hx : ∀ i, 1 ≤ x i ∧ x i ≤ Φ.dom i) :
    (Φ.SatisfiesSplicing x ↔ Φ.H.IsArcCut Φ.s Φ.t (Φ.selectedArcs x)) ∧
    (Φ.H.IsArcCut Φ.s Φ.t (Φ.selectedArcs x) →
      ∀ Z : Set A, Φ.H.IsArcCut Φ.s Φ.t Z → (Φ.selectedArcs x).ncard ≤ Z.ncard) := by sorry

end ConstrainedDirSep.STSep
