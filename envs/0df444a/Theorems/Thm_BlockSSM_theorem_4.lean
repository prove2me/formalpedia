-- Prove2me | Theorems.Thm_BlockSSM_theorem_4
-- name    : BlockSSM.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:26:14.087786+00:00
-- url     : https://prove2.me/theorems/513f92f7-17ac-48aa-bf83-51743a83bb6d
-- title:
--   Theorem 4: the exact dimension theorem, $n_b(G)=D_b(G)$
-- statement:
--   For every finite group $G$ and every block bound $b\ge 1$,
--   $$
--   n_b(G)=D_b(G).
--   $$
--   Here $n_b(G)$ is the minimum hidden dimension of a finite-state one-layer block-diagonal affine tracker of $G$ with blocks of size at most $b$, and $D_b(G)$ is the minimum dimension of a faithful complex representation, with all irreducible degrees at most $b$, of a finite group surjecting onto $G$. Both sides are $\infty$ when no feasible object exists, so the equality includes the statement that a tracker exists exactly when an admissible cover does.
--
--   This identifies an architectural quantity with a purely group-theoretic invariant; it is the main theorem of the paper.
--
--   Differences from the source:
--   - generalization: an integer block bound $b\ge 1$ → $b\in\mathbb N\cup\{\infty\}$ (`ℕ∞`) with $1\le b$; reason: every integer bound is a case through the cast, and $b=\infty$ is the unbounded case $D_\infty$ of Definition 2; the proof is the same
--   - encoding: hidden state space $\mathbb C^n$ with block-diagonal $A_g$ → the product $\prod_i\mathbb C^{n_i}$ with one matrix per block; reason: the same space split along the partition; the linear part is block-diagonal by construction
--   - encoding: a word $s=g_1\cdots g_T$ → a list with $g_1$ at the head; reason: the same words; the empty list is the empty word
--   - encoding: a finite group $H$ and a finite-dimensional complex representation $V$ in the minimum defining $D_b(G)$ → $H$ in the lowest universe and $V=\mathbb C^d$ as `Fin d → ℂ`; reason: every finite group has an isomorphic copy in `Type` and every $d$-dimensional representation is isomorphic to one on $\mathbb C^d$, so the set of dimensions is unchanged
--   - encoding: all irreducible degrees in $V$ at most $b$ → every irreducible subrepresentation of $V$ has dimension at most $b$; reason: by Maschke every irreducible constituent is isomorphic to an irreducible subrepresentation
--   - encoding: a minimum, with value $\infty$ on an empty feasible set → `sInf` in `ℕ∞`; reason: `sInf ∅ = ⊤`, and on a nonempty set of naturals `sInf` is the minimum
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 4, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_BlockSSM_trackerDim
import Definitions.Def_BlockSSM_coverDim

universe u

namespace BlockSSM

/-- **Theorem 4 (the exact dimension theorem).** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 4, p.2 (PDF p.3): "For every finite
group G and every b ≥ 1, n_b(G) = D_b(G)."

**Formalization Note.** Both sides live in `ℕ∞` and are `⊤` when no feasible object exists, so the
equality includes "no tracker exists iff no admissible cover exists". `b : ℕ∞` with `1 ≤ b` covers
every finite `b ≥ 1`, through the cast, and also the unbounded case `D_∞`, which the paper's proof
handles the same way. -/
theorem theorem_4 (G : Type u) [Group G] [Finite G] (b : ℕ∞) (hb : 1 ≤ b) :
    trackerDim G b = coverDim G b := by sorry

end BlockSSM
