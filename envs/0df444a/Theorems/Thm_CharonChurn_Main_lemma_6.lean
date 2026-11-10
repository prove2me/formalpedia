-- Prove2me | Theorems.Thm_CharonChurn_Main_lemma_6
-- name    : CharonChurn.Main.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:55:11.677538+00:00
-- url     : https://prove2.me/theorems/9d22a2b1-fbcf-4da6-b902-dd80d3e5109f
-- title:
--   Lemma 6 — vertex deletion and minimum degree
-- statement:
--   Let $G$ be a finite graph and $A\subseteq V(G)$. Then $\kappa(G-A)\ge\kappa(G)-|A|$ (in the integers). For every nonempty $G$, $\delta(G)\ge\kappa(G)$. If $|A|<\kappa(G)$ then $G-A$ is connected and has at least two vertices. Here $\kappa$ uses the conventions $\kappa=0$ for disconnected graphs and graphs with at most one vertex and $\kappa(K_h)=h-1$.
--
--   Differences from the source:
--   - encoding: a finite graph G and A ⊆ V(G) → the induced subgraph G[S] of an ambient simple graph on a finite vertex set S, with A ⊆ S; reason: every finite simple graph is of this form; same instances
--   - encoding: κ(G − A) ≥ κ(G) − |A| → the inequality cast to ℤ; reason: avoids truncated natural subtraction; same content
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), Lemma 6, p. 19 (PDF 19)

import Mathlib
import Definitions.Def_CharonChurn_Main_Connectivity

namespace CharonChurn.Main

/-- Lemma 6 (Vertex deletion and minimum degree), p. 19. For a finite graph `G[S]` and
`A ⊆ S`: `κ(G − A) ≥ κ(G) − |A|`; `δ(G) ≥ κ(G)` when `G` is nonempty; and if `|A| < κ(G)` then
`G − A` is connected with at least two vertices. -/
theorem lemma_6 {α : Type*} [DecidableEq α] (G : SimpleGraph α) (S A : Finset α) (hA : A ⊆ S) :
    (kappa G S : ℤ) - A.card ≤ kappa G (S \ A) ∧
    (∀ hS : S.Nonempty, kappa G S ≤ minDegree G S hS) ∧
    (A.card < kappa G S →
      (G.induce (↑(S \ A) : Set α)).Connected ∧ 2 ≤ (S \ A).card) := by sorry

end CharonChurn.Main
