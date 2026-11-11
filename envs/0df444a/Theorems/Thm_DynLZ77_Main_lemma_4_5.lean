-- Prove2me | Theorems.Thm_DynLZ77_Main_lemma_4_5
-- name    : DynLZ77.Main.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:21:39.16935+00:00
-- url     : https://prove2.me/theorems/a3f7c33a-8aa9-420f-84ea-ddcc2ea45d97
-- title:
--   Lemma 4.5 — $i + \mathrm{LPF}'_S(i)$ is non-decreasing
-- statement:
--   For every string $S$ and every $i\in[1..|S|-1]$,
--   $$i+\mathrm{LPF}'_S(i)\;\le\; i+1+\mathrm{LPF}'_S(i+1).$$
--   So the parents $i+\mathrm{LPF}'_S(i)$ in the LPF′-tree are non-decreasing in $i$. This monotonicity (from [BCR24, proof of Lemma 19]) underlies the irreducible positions $\mathrm{Ired}_S$ and the tree-oracle leaf test.
--
--   Differences from the source:
--   - encoding: i ∈ [|S| − 1] → 1 ≤ i and i + 1 ≤ |S|; reason: the same range, written without natural-number subtraction
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…), p. 17 (PDF 19), Lemma 4.5

import Mathlib
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

/-- **Lemma 4.5** (p. 17). For every string `S` and `i ∈ [1..|S| − 1]`,
`i + LPF′_S(i) ≤ i + 1 + LPF′_S(i + 1)`. -/
theorem lemma_4_5 {α : Type} [DecidableEq α] (S : List α) (i : ℕ) (hi1 : 1 ≤ i)
    (hi2 : i + 1 ≤ S.length) :
    i + lpf' S i ≤ i + 1 + lpf' S (i + 1) := by sorry

end DynLZ77.Main
