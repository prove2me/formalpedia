-- Prove2me | Theorems.Thm_DynLZ77_Main_lemma_9_7
-- name    : DynLZ77.Main.lemma_9_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:21:43.547538+00:00
-- url     : https://prove2.me/theorems/af238c63-eedb-4d00-a7ed-4248b91cfb40
-- title:
--   Lemma 9.7 — the trimmed LPF′-tree has $\tilde O(z)$ nodes
-- statement:
--   Let $T_S$ be the LPF′-tree of $S$ and $\mathrm{trimmed}(T_S)$ the tree induced by its internal (non-leaf) nodes. There are universal constants $c, C$ such that for every string $S$ over any alphabet, with $n=|S|$ and $z=|\mathrm{LZ77}(S)|$,
--   $$|\mathrm{trimmed}(T_S)|\le C\,(z+1)\,(\log_2(n+2))^{c}.$$
--   The LPF′-tree has $n+1$ nodes; this lemma is why a dynamic tree over its trimmed version fits in $\tilde O(z)$ space.
--
--   Differences from the source:
--   - encoding: |trimmed(T_S)| ∈ Õ(|LZ77(S)|), Õ(f) = O(f·log^c n) with n the length (footnote 1) → C·(z + 1)·(log₂(n + 2))^c with c, C universal; reason: the +1 and +2 keep the bound meaningful at z = 0 and n ≤ 1 and change nothing for n ≥ 2 (then z ≥ 1)
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…), p. 59 (PDF 61), Lemma 9.7

import Mathlib
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

/-- **Lemma 9.7** (p. 59). The trimmed LPF′-tree has `Õ(|LZ77(S)|)` nodes: there are universal
`c, C` with `|trimmed(T_S)| ≤ C·(z + 1)·(log₂(|S| + 2))^c` for every string `S`. -/
theorem lemma_9_7 : ∃ (c : ℕ) (C : ℝ), ∀ {α : Type} [DecidableEq α] (S : List α),
    ((internalNodes S).card : ℝ) ≤
      C * ((z S : ℝ) + 1) * Real.logb 2 ((S.length : ℝ) + 2) ^ c := by sorry

end DynLZ77.Main
