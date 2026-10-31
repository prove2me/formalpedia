-- Prove2me | Theorems.Thm_CombOpt_MinCut_prop_3_35
-- name    : CombOpt.MinCut.prop_3_35
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:01:59.491128+00:00
-- url     : https://prove2.me/theorems/e85f95d7-fa3e-4171-b581-a84e6ca143dc
-- title:
--   Proposition 3.35 — every cut of $G_{vw}$ is a cut of $G$; cuts of $G$ not separating $v,w$ are cuts of $G_{vw}$
-- statement:
--   Let $G=(V,E)$ be a finite capacitated multigraph and let $v,w$ be distinct nodes. Let $G_{vw}$ be the graph obtained by identifying $v$ with $w$; its edges form the subset $E\setminus\gamma(\{v,w\})$ of $E$. Then:
--
--   1. every cut of $G_{vw}$ is a cut of $G$: for every set $S'$ of nodes of $G_{vw}$ there is $S\subseteq V$ with $\delta_G(S)=\delta_{G_{vw}}(S')$;
--   2. every cut of $G$ that does not separate $v$ from $w$ is a cut of $G_{vw}$: for every $S\subseteq V$ containing both or neither of $v,w$ there is a set $S'$ of nodes of $G_{vw}$ with $\delta_{G_{vw}}(S')=\delta_G(S)$.
--
--   Consequently a minimum cut of a graph obtained by node identifications is a candidate minimum cut of $G$, and the only cuts lost are those separating identified nodes.
--
--   Differences from the source:
--   - encoding: a cut of $G_{vw}$, a set of edges of $G_{vw}$ → its image in $E$ under the inclusion of edge types (`Finset.map (Function.Embedding.subtype _)`); reason: the book's $E(G_{vw})=E\setminus\gamma(\{v,w\})$ is a subset of $E$, and the edges of $G_{vw}$ are those edges.
--   - encoding: the new node $x$ and the nodes $p\ne v,w$ → `none` and `some p` in `Option {a // a ≠ v ∧ a ≠ w}`; reason: Lean convention for $(V\setminus\{v,w\})\cup\{x\}$; same instances.
--   - generalization: $G$ connected with capacities $u_e>0$ (setting of §3.5, p. 72) → any finite multigraph with any real capacities; reason: the statement compares edge sets only, and its argument (take the preimage of $S'$, resp. the image of $S$) uses neither connectivity nor capacities; the book's case is an instance.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 3.35, p. 73 (PDF p. 82)

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph
import Definitions.Def_CombOpt_MinCut_CapGraph_delta
import Definitions.Def_CombOpt_MinCut_Separates
import Definitions.Def_CombOpt_MinCut_CapGraph_identify

namespace CombOpt.MinCut

open Classical in
/-- **Proposition 3.35 (cuts after node identification).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998),
Proposition 3.35, p. 73 (PDF p. 82): "Every cut of G_vw is a cut of G. Every cut of G that does not
separate v from w is a cut of G_vw."

For distinct nodes `v, w` of a finite multigraph `G`:
1. for every node set `S'` of `G_vw` there is `S ⊆ V` with `δ_G(S) = δ_{G_vw}(S')`;
2. for every `S ⊆ V` that does not separate `v` from `w` there is a node set `S'` of `G_vw` with
   `δ_{G_vw}(S') = δ_G(S)`.

**Formalization Note.** A cut is any set `δ(A)` (p. 12). An edge of `G_vw` is an edge of `G`
(`Subtype.val`), and the edge sets are compared after mapping `δ_{G_vw}(S')` into `E` by
`Subtype.val`. Capacities play no role. -/
theorem prop_3_35 {V E : Type*} [Fintype V] [Fintype E] (G : CapGraph V E) (v w : V)
    (hvw : v ≠ w) :
    (∀ S' : Finset (Option {a : V // a ≠ v ∧ a ≠ w}), ∃ S : Finset V,
      G.delta S = ((G.identify v w).delta S').map (Function.Embedding.subtype _)) ∧
    (∀ S : Finset V, ¬ Separates S v w → ∃ S' : Finset (Option {a : V // a ≠ v ∧ a ≠ w}),
      ((G.identify v w).delta S').map (Function.Embedding.subtype _) = G.delta S) := by sorry

end CombOpt.MinCut
