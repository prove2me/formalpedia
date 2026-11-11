-- Prove2me | Theorems.Thm_EuclidKSteiner_lemma_3_5
-- name    : EuclidKSteiner.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:25.124021+00:00
-- url     : https://prove2.me/theorems/05e358c6-83fd-431c-a3f4-222d8609d367
-- title:
--   Lemma 3.5 — completion formula $\mathrm{opt}(F)=w(M)+w(F)-\Phi(A)+w(\mathrm{MST}(C_F))$
-- statement:
--   Work in the graph setting with fixed terminal tree $M$, bottleneck lengths $\ell$ and attachment value $\Phi$. Let $F$ be a nonempty forest of Steiner edges each of whose components contains a terminal, with attachment set $A=V(F)\cap P$ and component graph $C_F$. Then
--   $$\mathrm{opt}(F)=w(M)+w(F)-\Phi(A)+w\bigl(\mathrm{MST}(C_F)\bigr).$$
--
--   The formula expresses the best completion of an attachment forest through $\Phi$ and a correction term for several components, which Lemma 4.1 absorbs into virtual edges.
--
--   Differences from the source:
--   - encoding: graph G with nonnegative edge weights, terminals P, candidates Q = V(G) \ P, G[P] connected, a fixed minimum spanning tree M of G[P], |P| ≥ 2 (§3 preamble) → the fields of GraphSetting; the existence of the minimum spanning tree M of G[P] encodes connectivity; reason: the standing assumptions of §§3–4, stated once
--   - encoding: opt(F), the minimum weight of a completion → a completion T with IsOptCompletion F T (least weight among all completions), whose existence is asserted; reason: an attained minimum, with no default value for an empty minimum
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Lemma 3.5, (3.4), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_EuclidKSteiner_GraphSetting

namespace EuclidKSteiner

/-- **Lemma 3.5 (Completion formula).** Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized
Tractability of Euclidean k-Steiner Tree*, STOC 2027 submission (manuscript sha256 75361687…),
Lemma 3.5, (3.4), p.11 (PDF p.13): "For every such forest F, opt(F) = w(M) + w(F) − Φ(A) +
w(MST(C_F))." ("such forest": a nonempty attachment forest each of whose components contains a
terminal, p.9.)

In the graph setting, for every nonempty forest `F` of Steiner edges with a terminal in each
component, with attachment set `A = V(F) ∩ P`, there is a minimum-weight completion `T` of `F` and
`w(T) = w(M) + w(F) − Φ(A) + w(MST(C_F))`.

**Formalization Note** `opt(F)` is the weight of a minimum-weight completion; its existence is part
of the conclusion. `C_F` is the complete graph on the Steiner components with edge weights
`min_{u ∈ A_i, v ∈ A_j} ℓ(u, v)`. -/
theorem lemma_3_5 {V : Type*} [Fintype V] [DecidableEq V] (S : GraphSetting V)
    (F : Finset (Sym2 V)) (hF : S.IsAttachmentForest F) (hne : F.Nonempty) :
    ∃ T : Finset (Sym2 V), S.IsOptCompletion F T ∧
      edgeSum S.w T = edgeSum S.w S.M + edgeSum S.w F - S.Phi (S.attachSet F) + S.mstCF F := by sorry

end EuclidKSteiner
