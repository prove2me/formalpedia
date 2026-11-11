-- Prove2me | Theorems.Thm_DynLZ77_Main_claim_8_10
-- name    : DynLZ77.Main.claim_8_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:21:40.074364+00:00
-- url     : https://prove2.me/theorems/af5e7bdf-b414-4594-a1e7-9afd03408cf5
-- title:
--   Claim 8.10 — each equality interval of an irreducible position contains exactly one phrase start
-- statement:
--   For $i\in\mathrm{Ired}_S$ let $E_i=[i..i+\mathrm{LPF}'_S(i))$ be its **equality interval**, and let $Z$ be the set of starting positions of the phrases of $\mathrm{LZ77}(S)$. Then
--   $$|E_i\cap Z|=1\qquad\text{for every } i\in\mathrm{Ired}_S.$$
--   This claim sits inside the proof of Lemma 1.2 (§8.2) and maps irreducible positions to phrase starts.
--
--   Differences from the source:
--   - reading: Ired_S = {1} ∪ {i > 1 | i + LPF′_S(i) ≠ i − 1 + LPF′_S(i − 1)} → Ired S ⊆ [1..|S|]: position 1 belongs to Ired_S only when |S| ≥ 1; reason: Ired_S is a set of positions of S ("irreducible LPF′ positions"); the empty string has no position 1, and with 1 ∈ Ired_ε the statement would be about a non-existent position
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…), p. 50 (PDF 52), Claim 8.10 (proof of Lemma 1.2, §8.2)

import Mathlib
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

/-- **Claim 8.10** (p. 50). For every `i ∈ Ired_S`, the equality interval
`E_i = [i..i + LPF′_S(i))` contains exactly one starting position of a phrase of `LZ77(S)`. -/
theorem claim_8_10 {α : Type} [DecidableEq α] (S : List α) (i : ℕ) (hi : i ∈ Ired S) :
    (Finset.Ico i (i + lpf' S i) ∩ ((LZ77 S).map Prod.fst).toFinset).card = 1 := by sorry

end DynLZ77.Main
