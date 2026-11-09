-- Prove2me | Theorems.Thm_DeMorganApprox_Main_lemma_5_6
-- name    : DeMorganApprox.Main.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:19.077413+00:00
-- url     : https://prove2.me/theorems/4f876e9f-4a51-4940-bd28-c7ab95cf8504
-- title:
--   Lemma 5.6 — the helper target h_C has balanced witness bound S_C = 1 + √(Σᵢ (Sᵢ² + Sᵢ))
-- statement:
--   Let $C$ be a heavy chain with top node $T$ (an internal node) and terminal targets $z_1,\dots,z_k$, and suppose each terminal's program is a vector-form span program computing its subformula, with balanced witness bound $S_i$. Let $P$ be the program obtained from the chain program by adding the fresh helper coordinate $h_C$ and the always-available connector $g_C=\cos\delta_C h_C-\sin\delta_C u_C$, with target $h_C$. Then
--
--   1. $P$ computes the subformula rooted at the top node of $C$;
--   2. $P$ is vector-form: $h_C$ and all listed vectors are unit;
--   3. its target is the helper coordinate vector $h_C$;
--   4. $h_C$ has balanced witness bound
--   $$S_C=1+\sqrt{\sum_{i=1}^k\left(S_i^2+S_i\right)} .$$
--
--   This is the recurrence that Lemma 5.7 solves; $S_C$ is the bound the parent chain uses for the terminal $h_C$.
--
--   Differences from the source:
--   - encoding: a heavy chain C of the formula, its top node and its terminal targets z₁,…,z_k → an internal formula T (isLeaf T = false) standing for the subformula at the top node of C, with all objects (chain, terminals, coordinates, columns) defined relative to T, the heavy child chosen by heavyDir with an arbitrary tie rule tie : List Bool → Bool, and terminals tie T the light children along the heavy path followed by the bottom leaf; reason: every chain top is an internal subformula and the program of a chain is built from its subtree only, so its objects are those of the whole program with the path prefix removed; the tie rule is universally quantified because the source allows either child at a tie (PDF p. 20)
--   - encoding: suppose zᵢ has balanced witness bound Sᵢ → every terminal's constructed program is vector-form, computes its subformula, and has balanced witness bound helperBound (the Sᵢ the construction uses: 1 for a leaf, S_D for a light child chain D); reason: zᵢ is the target of the vector-form span program for its leaf or light-child subformula (Definition 3.1 makes its vectors unit), and Sᵢ is the already constructed bound of zᵢ (PDF p. 21)
--   - encoding: a program with unit target h_C and balanced witness bound S_C → the constructed program program tie T with target the basis vector Coord.helper [], balanced bound helperBound tie T, and helperBound tie T = 1 + √Σ; reason: S_C is the bound the construction records for the chain; the second conjunct is the displayed formula
--   - encoding: a real Euclidean space H with unit vectors and the entrywise absolute value abs(V) → the coordinate space ι → ℝ for a finite type ι with its standard basis; squared norms are sums of squares; reason: abs(V) is only defined relative to a fixed orthonormal basis, which the construction provides (leaf and helper coordinates); finitely many listed vectors span a finite-dimensional subspace
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Lemma 5.6, PDF p. 22 (printed p. 20), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf; proof PDF pp. 22–23 (printed pp. 20–21)

import Mathlib
import Definitions.Def_DeMorganApprox_Main_HeavyChains

namespace DeMorganApprox.Main

/-- Lemma 5.6, PDF p. 22 (printed p. 20); proof PDF pp. 22–23. -/
theorem lemma_5_6 {m : ℕ} (tie : TieRule) (T : Formula m) (hT : T.isLeaf = false)
    (hterm : ∀ t ∈ terminals tie T,
      (program t.1 t.2).IsVectorForm ∧ (program t.1 t.2).Computes t.2.eval ∧
        (program t.1 t.2).HasBalancedBound (helperBound t.1 t.2)) :
    (program tie T).Computes T.eval ∧
      (program tie T).IsVectorForm ∧
      (∀ k, (program tie T).target k = basisV (.helper []) k.1) ∧
      (program tie T).HasBalancedBound (helperBound tie T) ∧
      helperBound tie T = 1 + Real.sqrt
        ((terminals tie T).map (fun t => helperBound t.1 t.2 ^ 2 + helperBound t.1 t.2)).sum
    := by sorry

end DeMorganApprox.Main
