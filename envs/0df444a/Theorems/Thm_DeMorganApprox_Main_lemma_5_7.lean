-- Prove2me | Theorems.Thm_DeMorganApprox_Main_lemma_5_7
-- name    : DeMorganApprox.Main.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:27.458201+00:00
-- url     : https://prove2.me/theorems/cdb929b8-be29-45d3-bd49-ac932f6aadaa
-- title:
--   Lemma 5.7 — S_C ≤ 100√n_C − 5 for every heavy chain; the root bound is O(√n)
-- statement:
--   For every heavy chain $C$, let $n_C$ be the number of leaves below its top node. The balanced witness bound $S_C$ of Lemma 5.6 satisfies
--   $$S_C\le 100\sqrt{n_C}-5 .$$
--   Consequently the root target has balanced witness bound $O(\sqrt n)$; explicitly, for every formula with $n$ leaves, the constructed program has balanced witness bound $S\le100\sqrt n$ (with $S=1$ for a single leaf).
--
--   This is the witness half of the main theorem: the extraction lemma turns a balanced bound $S$ into degree $O(S)$ and coefficient norm $2^{O(S)}$, so $S=O(\sqrt n)$ is what gives the exponents $\sqrt n$.
--
--   Differences from the source:
--   - encoding: a heavy chain C of the formula, its top node and its terminal targets z₁,…,z_k → an internal formula T (isLeaf T = false) standing for the subformula at the top node of C, with all objects (chain, terminals, coordinates, columns) defined relative to T, the heavy child chosen by heavyDir with an arbitrary tie rule tie : List Bool → Bool, and terminals tie T the light children along the heavy path followed by the bottom leaf; reason: every chain top is an internal subformula and the program of a chain is built from its subtree only, so its objects are those of the whole program with the path prefix removed; the tie rule is universally quantified because the source allows either child at a tie (PDF p. 20)
--   - generalization: Consequently, the root target has balanced witness bound O(√n) → for every formula T (also a single leaf) and every tie rule, the constructed program has balanced witness bound helperBound tie T, and helperBound tie T ≤ 100√n; reason: 100√n is an explicit instance of O(√n) and follows from the first clause, since 100√n − 5 ≤ 100√n; for a single leaf S = 1 ≤ 100
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Lemma 5.7, PDF p. 23 (printed p. 21), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf; proof PDF pp. 23–24 (printed pp. 21–22)

import Mathlib
import Definitions.Def_DeMorganApprox_Main_HeavyChains

namespace DeMorganApprox.Main

/-- Lemma 5.7, PDF p. 23 (printed p. 21); proof PDF pp. 23–24. Both clauses: the bound
`S_C ≤ 100 √n_C − 5` for every chain top, and the root bound (here `≤ 100 √n`). -/
theorem lemma_5_7 :
    (∀ (m : ℕ) (tie : TieRule) (T : Formula m), T.isLeaf = false →
      helperBound tie T ≤ 100 * Real.sqrt (T.leaves : ℝ) - 5) ∧
    (∀ (m : ℕ) (tie : TieRule) (T : Formula m),
      (program tie T).HasBalancedBound (helperBound tie T) ∧
        helperBound tie T ≤ 100 * Real.sqrt (T.leaves : ℝ)) := by sorry

end DeMorganApprox.Main
