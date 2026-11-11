-- Prove2me | Theorems.Thm_EuclidKSteiner_lemma_3_1
-- name    : EuclidKSteiner.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:28.533208+00:00
-- url     : https://prove2.me/theorems/2f7a1184-0b72-4d29-9938-1d9d6f8c0355
-- title:
--   Lemma 3.1 — backbone edges can be taken from $M$
-- statement:
--   Work in the graph setting: a graph $G$ with nonnegative edge weights, terminals $P$ with $|P|\ge2$, candidates $Q=V(G)\setminus P$, and a fixed minimum spanning tree $M$ of $G[P]$.
--
--   Let $F$ be a forest of Steiner edges with a terminal in each component. Then among the trees of $G$ on $P\cup V(F)$ whose Steiner edges are exactly $F$ there is one of minimum weight all of whose backbone edges belong to $M$.
--
--   The lemma lets every solution be written as $M$ minus some edges plus an attachment forest, which is the starting point of the completion formula.
--
--   Differences from the source:
--   - encoding: graph G with nonnegative edge weights, terminals P, candidates Q = V(G) \ P, G[P] connected, a fixed minimum spanning tree M of G[P], |P| ≥ 2 (§3 preamble) → the fields of GraphSetting; the existence of the minimum spanning tree M of G[P] encodes connectivity; reason: the standing assumptions of §§3–4, stated once
--   - encoding: a minimum-weight tree on P ∪ V(F) with Steiner edges exactly F → a minimum-weight completion of F (a tree of G spanning P ∪ V(F), containing F, other edges backbone edges), with its edges outside F in M; reason: a tree on P ∪ V(F) has Steiner edges exactly F iff it contains F and its other edges join two terminals; existence of the minimum is part of the claim
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Lemma 3.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EuclidKSteiner_GraphSetting

namespace EuclidKSteiner

/-- **Lemma 3.1.** Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean
k-Steiner Tree*, STOC 2027 submission (manuscript sha256 75361687…), Lemma 3.1, p.9 (PDF p.11):
"Let F be a forest of Steiner edges with a terminal in each component. Some minimum-weight tree on
P ∪ V(F) with Steiner edges exactly F has all backbone edges in M."

In the graph setting (a graph `G` with nonnegative weights, terminals `P`, `|P| ≥ 2`, a fixed minimum
spanning tree `M` of `G[P]`), for every forest `F` of Steiner edges with a terminal in each component
there is a minimum-weight completion of `F` (a tree of `G` spanning `P ∪ V(F)` that contains `F`, all
of whose other edges are backbone edges) whose edges outside `F` all belong to `M`.

**Formalization Note** A tree of `G` on `P ∪ V(F)` has Steiner edges exactly `F` if and only if it
contains `F` and its other edges join two terminals, i.e. it is a completion of `F`
(`IsCompletion`). The existence of a minimum-weight such tree is part of the conclusion. -/
theorem lemma_3_1 {V : Type*} [Fintype V] [DecidableEq V] (S : GraphSetting V)
    (F : Finset (Sym2 V)) (hF : S.IsAttachmentForest F) :
    ∃ T : Finset (Sym2 V), S.IsOptCompletion F T ∧ ∀ e ∈ T, e ∉ F → e ∈ S.M := by sorry

end EuclidKSteiner
