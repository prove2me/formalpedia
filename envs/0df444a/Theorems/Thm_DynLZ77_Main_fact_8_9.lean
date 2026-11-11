-- Prove2me | Theorems.Thm_DynLZ77_Main_fact_8_9
-- name    : DynLZ77.Main.fact_8_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:22:01.389728+00:00
-- url     : https://prove2.me/theorems/4c306c85-c55a-4152-a68a-d95c83486f8e
-- title:
--   Fact 8.9 — a substring with no earlier occurrence contains an LZ77 phrase start
-- statement:
--   Let $S$ be a string and $S[i..j]$ a substring ($1\le i\le j\le|S|$) that does not occur at any position $i'<i$. Then some phrase $[x..y]\in\mathrm{LZ77}(S)$ starts inside it:
--   $$\exists\,[x..y]\in\mathrm{LZ77}(S):\ x\in[i..j].$$
--   This is [Lew13, Lemma 3], the usual basis of LZ77-compressed indexes; in §8 it places a phrase start inside every leftmost occurrence.
--
--   Differences from the source:
--   - reading: a substring S[i..j] → 1 ≤ i ≤ j ≤ |S|; reason: p. 15 calls S[i..j] the substring that starts at index i and ends at index j, so it is nonempty; for an empty S[1..0] the conclusion has no position to offer
--   - encoding: phrase [x..y] ∈ LZ77(S) → (x, y) ∈ LZ77 S; reason: phrases are position pairs
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…), p. 50 (PDF 52), Fact 8.9

import Mathlib
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

/-- **Fact 8.9** (p. 50). If the substring `S[i..j]` does not occur at any position `i′ < i`, some
phrase `[x..y]` of `LZ77(S)` starts at a position `x ∈ [i..j]`. -/
theorem fact_8_9 {α : Type} [DecidableEq α] (S : List α) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ S.length)
    (hnew : ∀ i' : ℕ, 1 ≤ i' → i' < i → sub S i' (i' + (j - i)) ≠ sub S i j) :
    ∃ x y : ℕ, (x, y) ∈ LZ77 S ∧ i ≤ x ∧ x ≤ j := by sorry

end DynLZ77.Main
