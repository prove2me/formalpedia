-- Prove2me | Theorems.Thm_DynLZ77_Main_lemma_1_2
-- name    : DynLZ77.Main.lemma_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:22:03.713306+00:00
-- url     : https://prove2.me/theorems/9583affc-20ce-41c4-a823-7f340f3a202d
-- title:
--   Lemma 1.2 — a string has $O(z\log^3 n)$ irreducible LPF′ positions
-- statement:
--   There is a universal constant $C$ such that for every string $S$ over any alphabet, with $z=|\mathrm{LZ77}(S)|$,
--   $$|\mathrm{Ired}_S|\le C\,z\,(1+\log_2|S|)^3 .$$
--   This is the paper's combinatorial contribution: the number of irreducible LPF′ positions, which can be $\Theta(n)$ for incompressible strings, is bounded by the LZ77 size up to polylogarithmic factors. It is what lets the LPF′-tree be stored in compressed space (Lemma 9.7).
--
--   Differences from the source:
--   - encoding: |Ired_S| = O(z log³|S|) → |Ired S| ≤ C·z·(1 + log₂|S|)³ with C universal; reason: log₂|S| is 0 at |S| = 1 and undefined at |S| = 0; the +1 is O(·) slack and changes nothing for |S| ≥ 2; the exponent 3 is kept
--   - reading: Ired_S = {1} ∪ {i > 1 | i + LPF′_S(i) ≠ i − 1 + LPF′_S(i − 1)} → Ired S ⊆ [1..|S|]: position 1 belongs to Ired_S only when |S| ≥ 1; reason: Ired_S is a set of positions of S ("irreducible LPF′ positions"); the empty string has no position 1, and with 1 ∈ Ired_ε the statement would be about a non-existent position
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…), p. 2 (PDF 4), Lemma 1.2 (restated p. 47 (PDF 49); proved in §8.2, pp. 50-53 (PDF 52-55))

import Mathlib
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

/-- **Lemma 1.2** (p. 2; proved in §8.2). There is a universal constant `C` such that every
string `S` has `|Ired_S| ≤ C·z·(1 + log₂|S|)³`, `z = |LZ77(S)|`. -/
theorem lemma_1_2 : ∃ C : ℝ, ∀ {α : Type} [DecidableEq α] (S : List α),
    ((Ired S).card : ℝ) ≤ C * (z S : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 3 := by sorry

end DynLZ77.Main
