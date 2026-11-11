-- Prove2me | Theorems.Thm_DynLZ77_Main_lemma_8_8
-- name    : DynLZ77.Main.lemma_8_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:21:45.591194+00:00
-- url     : https://prove2.me/theorems/90707468-0234-4401-8cd8-81d34c0687c9
-- title:
--   Lemma 8.8 — a string of period at least $p$ has a substring of every length $w\in[2p..|S|]$ with period at least $p$
-- statement:
--   Let $S$ be a string and $p$ an integer with $\mathrm{per}(S)\ge p$. For every integer $w\in[2p..|S|]$ there is a substring $S_w$ of $S$ of length $w$ with
--   $$\mathrm{per}(S_w)\ge p.$$
--   In the proof of Lemma 1.2 this finds a window of length $3\tau-1$ that is not $\tau/3$-periodic, which the density property of a synchronizing set then turns into a synchronizing position.
--
--   Differences from the source:
--   - encoding: every integer w ∈ [2p..|S|] → every natural number w with 2p ≤ w ≤ |S| (p an integer); reason: a substring has a length w ≥ 0; a negative w (possible only when p < 0) names no substring
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…), p. 50 (PDF 52), Lemma 8.8

import Mathlib
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

/-- **Lemma 8.8** (p. 50). Let `p` be an integer with `per(S) ≥ p`. For every integer
`w ∈ [2p..|S|]` there is a substring `S_w` of `S` of length `w` with `per(S_w) ≥ p`. -/
theorem lemma_8_8 {α : Type} (S : List α) (p : ℤ) (hp : p ≤ (per S : ℤ)) (w : ℕ)
    (hw1 : 2 * p ≤ (w : ℤ)) (hw2 : w ≤ S.length) :
    ∃ i : ℕ, 1 ≤ i ∧ i + w ≤ S.length + 1 ∧ p ≤ (per (sub S i (i + w - 1)) : ℤ) := by sorry

end DynLZ77.Main
