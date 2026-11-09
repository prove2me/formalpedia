-- Prove2me | Theorems.Thm_DeMorganApprox_Main_lemma_5_5
-- name    : DeMorganApprox.Main.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:10.880195+00:00
-- url     : https://prove2.me/theorems/83a25920-514a-4072-9c5b-7b3b13d47e1d
-- title:
--   Lemma 5.5 — the internal chain target u_C satisfies (A_C+1)B_C = Σᵢ (Sᵢ² + Sᵢ)
-- statement:
--   Let $C$ be a heavy chain with top node $T$ (an internal node) and terminal targets $z_1,\dots,z_k$, each a leaf coordinate or the helper coordinate of a light child chain. Suppose each terminal's program is a vector-form span program computing its subformula, with balanced witness bound $S_i$ ($S_i=1$ for a leaf). Let $P_C$ be the chain program obtained by applying the gate composition of Lemma 5.3 along $C$, with internal target $u_C$ and parameters $(A_C,B_C)$. Then
--
--   1. $P_C$ computes the subformula rooted at $T$;
--   2. $P_C$ is vector-form: $u_C$ and all its listed vectors (including the OR rotation vectors) are unit;
--   3. $(A_C,B_C)$ are witness parameters of $u_C$, and
--   $$(A_C+1)B_C=\sum_{i=1}^k\left(S_i^2+S_i\right);$$
--   4. $u_C\in\operatorname{span}\{z_1,\dots,z_k\}$ is a nonnegative linear combination of $z_1,\dots,z_k$.
--
--   The nonnegativity in 4 is what makes the rotation vectors of the chain almost orthonormal after taking absolute values (Lemma 5.8).
--
--   Differences from the source:
--   - encoding: a heavy chain C of the formula, its top node and its terminal targets z₁,…,z_k → an internal formula T (isLeaf T = false) standing for the subformula at the top node of C, with all objects (chain, terminals, coordinates, columns) defined relative to T, the heavy child chosen by heavyDir with an arbitrary tie rule tie : List Bool → Bool, and terminals tie T the light children along the heavy path followed by the bottom leaf; reason: every chain top is an internal subformula and the program of a chain is built from its subtree only, so its objects are those of the whole program with the path prefix removed; the tie rule is universally quantified because the source allows either child at a tie (PDF p. 20)
--   - encoding: suppose zᵢ has balanced witness bound Sᵢ → every terminal's constructed program is vector-form, computes its subformula, and has balanced witness bound helperBound (the Sᵢ the construction uses: 1 for a leaf, S_D for a light child chain D); reason: zᵢ is the target of the vector-form span program for its leaf or light-child subformula (Definition 3.1 makes its vectors unit), and Sᵢ is the already constructed bound of zᵢ (PDF p. 21)
--   - encoding: u_C is a nonnegative linear combination of z₁, …, z_k (hence u_C ∈ span{z₁, …, z_k}) → every coordinate of u_C is nonnegative and u_C vanishes outside the terminal coordinates terminalKeys tie T; reason: the terminals are distinct standard basis vectors, so the two statements are equivalent
--   - encoding: the OR gates along the chain may also introduce always-available rotation vectors → carried by the definition: the chain program's columns include the rotation column of every OR node on the chain (chainCols); no separate clause; reason: the sentence describes the construction and asserts nothing further
--   - encoding: a real Euclidean space H with unit vectors and the entrywise absolute value abs(V) → the coordinate space ι → ℝ for a finite type ι with its standard basis; squared norms are sums of squares; reason: abs(V) is only defined relative to a fixed orthonormal basis, which the construction provides (leaf and helper coordinates); finitely many listed vectors span a finite-dimensional subspace
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Lemma 5.5, PDF p. 21 (printed p. 19), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf; proof PDF p. 22 (printed p. 20)

import Mathlib
import Definitions.Def_DeMorganApprox_Main_HeavyChains

namespace DeMorganApprox.Main

/-- Lemma 5.5, PDF p. 21 (printed p. 19); proof PDF p. 22. `T` is the subformula at the top node
of the chain `C`; the hypotheses are those of the lemma on the terminal programs. -/
theorem lemma_5_5 {m : ℕ} (tie : TieRule) (T : Formula m) (hT : T.isLeaf = false)
    (hterm : ∀ t ∈ terminals tie T,
      (program t.1 t.2).IsVectorForm ∧ (program t.1 t.2).Computes t.2.eval ∧
        (program t.1 t.2).HasBalancedBound (helperBound t.1 t.2)) :
    (chainProgram tie T).Computes T.eval ∧
      (chainProgram tie T).IsVectorForm ∧
      (chainProgram tie T).HasWitnessParams (chainParams tie T).1 (chainParams tie T).2 ∧
      ((chainParams tie T).1 + 1) * (chainParams tie T).2 =
        ((terminals tie T).map (fun t => helperBound t.1 t.2 ^ 2 + helperBound t.1 t.2)).sum ∧
      (∀ k, 0 ≤ chainU tie T k) ∧
      (∀ k, k ∉ terminalKeys tie T → chainU tie T k = 0) := by sorry

end DeMorganApprox.Main
