-- Prove2me | Theorems.Thm_BlockSSM_coverDim_le_hiddenDim
-- name    : BlockSSM.coverDim_le_hiddenDim
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:23:48.712331+00:00
-- url     : https://prove2.me/theorems/c149eec8-8796-4e65-98eb-32e1f0341290
-- title:
--   A tracker contains a cover: $D_b(G)\le n$
-- statement:
--   Let $G$ be a finite group, $b\ge 1$, and let $T$ be any finite-state tracker of $G$ with block bound $b$ and hidden dimension $n$, whose decoder tracks $G$. Then
--   $$
--   D_b(G)\le n.
--   $$
--   No invertibility of the transitions and no bound on matrix products is assumed.
--
--   This is the lower-bound half of the exact dimension theorem, obtained by combining Lemmas 5, 6 and 7.
--
--   Differences from the source:
--   - generalization: an integer block bound $b\ge 1$ → $b\in\mathbb N\cup\{\infty\}$ (`ℕ∞`) with $1\le b$; reason: every integer bound is a case through the cast, and $b=\infty$ is the unbounded case $D_\infty$ of Definition 2; the proof is the same
--   - encoding: hidden state space $\mathbb C^n$ with block-diagonal $A_g$ → the product $\prod_i\mathbb C^{n_i}$ with one matrix per block; reason: the same space split along the partition; the linear part is block-diagonal by construction
--   - encoding: a finite group $H$ and a finite-dimensional complex representation $V$ in the minimum defining $D_b(G)$ → $H$ in the lowest universe and $V=\mathbb C^d$ as `Fin d → ℂ`; reason: every finite group has an isomorphic copy in `Type` and every $d$-dimensional representation is isomorphic to one on $\mathbb C^d$, so the set of dimensions is unchanged
--   - encoding: all irreducible degrees in $V$ at most $b$ → every irreducible subrepresentation of $V$ has dimension at most $b$; reason: by Maschke every irreducible constituent is isomorphic to an irreducible subrepresentation
--   - encoding: a minimum, with value $\infty$ on an empty feasible set → `sInf` in `ℕ∞`; reason: `sInf ∅ = ⊤`, and on a nonempty set of naturals `sInf` is the minimum
--   - encoding: a word $s=g_1\cdots g_T$ → a list with $g_1$ at the head; reason: the same words; the empty list is the empty word
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), §3.2, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_BlockSSM_Tracker_Tracks
import Definitions.Def_BlockSSM_Tracker_IsFiniteState
import Definitions.Def_BlockSSM_coverDim

universe u

namespace BlockSSM

/-- **A tracker contains a cover.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), §3.2, p.4 (PDF p.5): "Applying these lemmas gives a cover
H ↠ G with an admissible faithful representation of dimension at most n. Consequently D_b(G) ≤ n,
proving theorem 4. This argument does not assume invertible transitions or bounded matrix products."

**Formalization Note.** `T` is an arbitrary finite-state tracker of `G`: nothing is assumed about its
matrices, biases or decoder. -/
theorem coverDim_le_hiddenDim (G : Type u) [Group G] [Finite G] (b : ℕ∞) (hb : 1 ≤ b)
    (T : Tracker G b) (ht : T.Tracks) (hf : T.IsFiniteState) :
    coverDim G b ≤ (T.hiddenDim : ℕ∞) := by sorry

end BlockSSM
