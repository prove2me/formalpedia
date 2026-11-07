-- Prove2me | Theorems.Thm_BlockSSM_trackerDim_le_coverDim
-- name    : BlockSSM.trackerDim_le_coverDim
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:26:00.409223+00:00
-- url     : https://prove2.me/theorems/31a39163-da7c-42f6-81e2-d9ba4c2a1ee6
-- title:
--   A cover gives a tracker: $n_b(G)\le D_b(G)$
-- statement:
--   For every finite group $G$ and every block bound $b\ge 1$,
--   $$
--   n_b(G)\le D_b(G),
--   $$
--   where $n_b(G)$ is the minimum hidden dimension of a finite-state tracker of $G$ and $D_b(G)$ is the cover invariant. The inequality is automatic when $D_b(G)=\infty$.
--
--   This is the upper-bound half of the exact dimension theorem.
--
--   Differences from the source:
--   - generalization: an integer block bound $b\ge 1$ → $b\in\mathbb N\cup\{\infty\}$ (`ℕ∞`) with $1\le b$; reason: every integer bound is a case through the cast, and $b=\infty$ is the unbounded case $D_\infty$ of Definition 2; the proof is the same
--   - encoding: hidden state space $\mathbb C^n$ with block-diagonal $A_g$ → the product $\prod_i\mathbb C^{n_i}$ with one matrix per block; reason: the same space split along the partition; the linear part is block-diagonal by construction
--   - encoding: a finite group $H$ and a finite-dimensional complex representation $V$ in the minimum defining $D_b(G)$ → $H$ in the lowest universe and $V=\mathbb C^d$ as `Fin d → ℂ`; reason: every finite group has an isomorphic copy in `Type` and every $d$-dimensional representation is isomorphic to one on $\mathbb C^d$, so the set of dimensions is unchanged
--   - encoding: all irreducible degrees in $V$ at most $b$ → every irreducible subrepresentation of $V$ has dimension at most $b$; reason: by Maschke every irreducible constituent is isomorphic to an irreducible subrepresentation
--   - encoding: a minimum, with value $\infty$ on an empty feasible set → `sInf` in `ℕ∞`; reason: `sInf ∅ = ⊤`, and on a nonempty set of naturals `sInf` is the minimum
--   - encoding: a word $s=g_1\cdots g_T$ → a list with $g_1$ at the head; reason: the same words; the empty list is the empty word
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), §3.1, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_BlockSSM_trackerDim
import Definitions.Def_BlockSSM_coverDim

universe u

namespace BlockSSM

/-- **A cover gives a tracker.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), §3.1, p.3 (PDF p.4): "Thus n_b(G) ≤ D_b(G)."

**Formalization Note.** Inequality in `ℕ∞`; it is automatic when `D_b(G) = ∞`, as the paper says.
`b : ℕ∞`, see `theorem_4`. -/
theorem trackerDim_le_coverDim (G : Type u) [Group G] [Finite G] (b : ℕ∞) (hb : 1 ≤ b) :
    trackerDim G b ≤ coverDim G b := by sorry

end BlockSSM
