-- Prove2me | Theorems.Thm_AgnosticTNS_lemma_2_5
-- name    : AgnosticTNS.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:34:23.523832+00:00
-- url     : https://prove2.me/theorems/c810c562-79fb-41b4-9acc-cb4416f01ae4
-- title:
--   Lemma 2.5 — laminarity of learning sequences
-- statement:
--   Let $\mathcal L=(S_i,I_i,F_i)_{i=1}^L$ be a learning sequence. For any two indices $i,j\in[L]$ the sets $S_i$ and $S_j$ are either disjoint or one contains the other. In particular, if $j<i$, then either $S_j\subseteq S_i$ or $S_j\cap S_i=\emptyset$.
--
--   So every earlier step of the algorithm acts entirely inside or entirely outside the current set $S_i$.
--
--   Differences from the source:
--   - encoding: steps $[L]$, root $L$, $I_i\subseteq[i-1]$, condition 4 of Definition 2.3 → steps `Fin L`, root $L-1$, $j\in I_i\Rightarrow j<i$, each non-root step in exactly one $I_i$ and the root in none; reason: Lean convention; equivalent formulation of Definition 2.3
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Lemma 2.5, p.13

import Mathlib
import Definitions.Def_AgnosticTNS_LearningSequence

namespace AgnosticTNS

/-- **Lemma 2.5 (Laminarity of learning sequences)**, p.13 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). For a learning sequence
`(S_i, I_i, F_i)_{i=1}^L` and any two indices `i, j`, the sets `S_i` and `S_j` are disjoint or one
contains the other; in particular, if `j < i` then `S_j ⊆ S_i` or `S_j ∩ S_i = ∅`. -/
theorem lemma_2_5 {n : ℕ} (Ls : LearningSequence n) :
    (∀ i j, Disjoint (Ls.S i) (Ls.S j) ∨ Ls.S i ⊆ Ls.S j ∨ Ls.S j ⊆ Ls.S i) ∧
      ∀ i j, j < i → Ls.S j ⊆ Ls.S i ∨ Disjoint (Ls.S j) (Ls.S i) := by sorry

end AgnosticTNS
