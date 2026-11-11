-- Prove2me | Theorems.Thm_EuclidKSteiner_lemma_4_1
-- name    : EuclidKSteiner.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:32.741841+00:00
-- url     : https://prove2.me/theorems/8e986e71-cff2-4e92-a90a-d9c62d593f2c
-- title:
--   Lemma 4.1 — augmented trees: $\mathrm{opt}(F)=w(M)+w(T)-\Phi(A)$ and the converse inequality
-- statement:
--   Work in the graph setting.
--
--   1. Let $F$ be a nonempty attachment forest in which every component contains a terminal, with attachment set $A$. One can add $\mathrm{cc}(F)-1$ virtual edges to obtain an augmented tree $T$ (terminal set $A$, candidate set $V(F)\setminus P$) such that
--   $$\mathrm{opt}(F)=w(M)+w(T)-\Phi(A).$$
--   2. Conversely, for every augmented tree $T$ with terminal set $A$ and attachment forest $F$,
--   $$w(M)+w(T)-\Phi(A)\ge\mathrm{opt}(F).$$
--
--   Together the two clauses reduce the problem to minimizing $w(T)-\Phi(A)$ over small augmented trees.
--
--   Differences from the source:
--   - encoding: graph G with nonnegative edge weights, terminals P, candidates Q = V(G) \ P, G[P] connected, a fixed minimum spanning tree M of G[P], |P| ≥ 2 (§3 preamble) → the fields of GraphSetting; the existence of the minimum spanning tree M of G[P] encodes connectivity; reason: the standing assumptions of §§3–4, stated once
--   - encoding: opt(F), the minimum weight of a completion → a completion T with IsOptCompletion F T (least weight among all completions), whose existence is asserted; reason: an attained minimum, with no default value for an empty minimum
--   - encoding: an augmented tree on A ∪ S with Steiner and virtual edges → IsAugTree A S T: T a spanning tree of A ∪ S using Steiner edges of G inside A ∪ S and pairs of distinct terminals of A, every terminal of A adjacent to S; w(T) by augWeight, the attachment forest by augForest; reason: the definition of §4.1, p.15
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Lemma 4.1, (4.1), (4.2), p.15 (PDF p.17)

import Mathlib
import Definitions.Def_EuclidKSteiner_GraphSetting

namespace EuclidKSteiner

/-- **Lemma 4.1 (Augmented trees).** Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability
of Euclidean k-Steiner Tree*, STOC 2027 submission (manuscript sha256 75361687…), Lemma 4.1, (4.1),
(4.2), p.15 (PDF p.17): "Let F be a nonempty attachment forest such that each connected component
contains at least one terminal from P, and let A be its attachment set. One can add cc(F) − 1
virtual edges to obtain an augmented tree T such that opt(F) = w(M) + w(T) − Φ(A). (4.1) Conversely,
let T be any augmented tree with terminal set A and attachment forest F. Then
w(M) + w(T) − Φ(A) ≥ opt(F). (4.2)"

1. For every nonempty forest `F` of Steiner edges with a terminal in each component and attachment
   set `A`, there is a set of exactly `cc(F) − 1` virtual edges (pairs of distinct terminals of `A`)
   whose union with `F` is an augmented tree `T` with terminal set `A` and candidate set
   `V(F) \ P`, and a minimum-weight completion of `F` has weight `w(M) + w(T) − Φ(A)`.
2. For every augmented tree `T` with terminal set `A`, its attachment forest `F` (the Steiner edges of
   `T`) has a minimum-weight completion of weight at most `w(M) + w(T) − Φ(A)`.

**Formalization Note** `w(T)` (`augWeight`) charges original weights to Steiner edges and `ℓ` to
virtual edges. `opt(F)` is the weight of a minimum-weight completion; its existence is part of both
clauses. -/
theorem lemma_4_1 {V : Type*} [Fintype V] [DecidableEq V] (S : GraphSetting V) :
    (∀ F : Finset (Sym2 V), S.IsAttachmentForest F → F.Nonempty →
      ∃ Vv : Finset (Sym2 V), Vv ⊆ completeEdges (S.attachSet F) ∧ Vv.card = GraphSetting.ccF F - 1 ∧
        S.IsAugTree (S.attachSet F) (GraphSetting.verts F \ S.P) (F ∪ Vv) ∧
        ∃ T' : Finset (Sym2 V), S.IsOptCompletion F T' ∧
          edgeSum S.w T' = edgeSum S.w S.M + S.augWeight (F ∪ Vv) - S.Phi (S.attachSet F)) ∧
    (∀ (A C : Finset V) (T : Finset (Sym2 V)), S.IsAugTree A C T →
      ∃ T' : Finset (Sym2 V), S.IsOptCompletion (S.augForest T) T' ∧
        edgeSum S.w T' ≤ edgeSum S.w S.M + S.augWeight T - S.Phi A) := by sorry

end EuclidKSteiner
