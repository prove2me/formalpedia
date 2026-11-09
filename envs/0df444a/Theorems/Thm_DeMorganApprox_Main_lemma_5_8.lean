-- Prove2me | Theorems.Thm_DeMorganApprox_Main_lemma_5_8
-- name    : DeMorganApprox.Main.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:03.088514+00:00
-- url     : https://prove2.me/theorems/496e3366-a0bd-4ae9-bbaf-19a98ac61ec9
-- title:
--   Lemma 5.8 — every chain block V_C of rotation and connector vectors has ‖abs(V_C)‖ = O(1)
-- statement:
--   For each heavy chain $C$, let $V_C$ be the matrix whose columns are the available vectors assigned to $C$: the OR-rotation vectors $r_j$ of $C$ and the connector $g_C$. Then
--   $$\|\operatorname{abs}(V_C)\|=O(1),$$
--   that is, there is one absolute constant $c$ such that $\|\operatorname{abs}(V_C)y\|_2\le c\|y\|_2$ for every chain $C$ of every formula, every tie rule, and every coefficient vector $y$.
--
--   This is the local half of the norm bound; Lemma 5.9 assembles the blocks.
--
--   Differences from the source:
--   - encoding: a heavy chain C of the formula, its top node and its terminal targets z₁,…,z_k → an internal formula T (isLeaf T = false) standing for the subformula at the top node of C, with all objects (chain, terminals, coordinates, columns) defined relative to T, the heavy child chosen by heavyDir with an arbitrary tie rule tie : List Bool → Bool, and terminals tie T the light children along the heavy path followed by the bottom leaf; reason: every chain top is an internal subformula and the program of a chain is built from its subtree only, so its objects are those of the whole program with the path prefix removed; the tie rule is universally quantified because the source allows either child at a tie (PDF p. 20)
--   - reading: ‖abs(V_C)‖ = O(1) → ∃ c chosen before m, the tie rule and T, with AbsNormLE (operator-norm bound) c; reason: O(1) is one absolute constant; the source's proof gives 4
--   - encoding: the matrix V_C with rows the ambient coordinates → columns chainBlockCols tie T (rotation columns of the chain and the connector), rows all coordinates of the program of T; reason: rows on which no column is supported contribute zero to ‖abs(V_C)y‖
--   - encoding: a real Euclidean space H with unit vectors and the entrywise absolute value abs(V) → the coordinate space ι → ℝ for a finite type ι with its standard basis; squared norms are sums of squares; reason: abs(V) is only defined relative to a fixed orthonormal basis, which the construction provides (leaf and helper coordinates); finitely many listed vectors span a finite-dimensional subspace
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Lemma 5.8, PDF p. 25 (printed p. 23), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf; proof PDF pp. 25–27 (printed pp. 23–25)

import Mathlib
import Definitions.Def_DeMorganApprox_Main_HeavyChains

namespace DeMorganApprox.Main

/-- Lemma 5.8, PDF p. 25 (printed p. 23); proof PDF pp. 25–27. One absolute constant `c` for
every chain block. -/
theorem lemma_5_8 :
    ∃ c : ℝ, ∀ (m : ℕ) (tie : TieRule) (T : Formula m), T.isLeaf = false →
      AbsNormLE (fun (j : {j // j ∈ chainBlockCols tie T}) (k : {k // k ∈ fullCoords tie T}) =>
        colVec tie T j.1 k.1) c := by sorry

end DeMorganApprox.Main
