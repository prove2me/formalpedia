-- Prove2me | Theorems.Thm_CharonChurn_Main_lemma_7
-- name    : CharonChurn.Main.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:55:16.193825+00:00
-- url     : https://prove2.me/theorems/cc133326-cc6b-48c5-8bab-e10e3d64dd0a
-- title:
--   Lemma 7 — attachment to a connected core
-- statement:
--   Let $Q$ be a finite graph, $K\subseteq V(Q)$ and $h\ge0$ an integer. If $\kappa(Q[K])>h$ and $|N_Q(v)\cap K|>h$ for every $v\in V(Q)\setminus K$, then $\kappa(Q)>h$.
--
--   Differences from the source:
--   - encoding: a graph Q with K ⊆ V(Q) and an integer h ≥ 0 → Q[S] for an ambient simple graph on a finite set S, K ⊆ S, and h : ℕ; reason: every finite simple graph is of this form, and nonnegative integers are naturals
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), Lemma 7, p. 19 (PDF 19)

import Mathlib
import Definitions.Def_CharonChurn_Main_Connectivity

namespace CharonChurn.Main

/-- Lemma 7 (Attachment to a connected core), p. 19. If `κ(Q[K]) > h` and every vertex of
`Q` outside `K` has more than `h` neighbours in `K`, then `κ(Q) > h`. -/
theorem lemma_7 {α : Type*} [DecidableEq α] (Q : SimpleGraph α) (S K : Finset α) (hK : K ⊆ S)
    (h : ℕ) (hcore : h < kappa Q K) (hattach : ∀ v ∈ S \ K, h < (nbrsIn Q K v).card) :
    h < kappa Q S := by sorry

end CharonChurn.Main
