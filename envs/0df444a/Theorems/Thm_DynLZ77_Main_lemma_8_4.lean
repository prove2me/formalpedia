-- Prove2me | Theorems.Thm_DynLZ77_Main_lemma_8_4
-- name    : DynLZ77.Main.lemma_8_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:21:44.487108+00:00
-- url     : https://prove2.me/theorems/7cad5be2-70c3-4c3d-81eb-f5f1cea85010
-- title:
--   Lemma 8.4 — an $I$-local $\tau$-synchronizing set of size $O(|I|)$ exists
-- statement:
--   There is a universal constant $C$ such that for every alphabet, every string $T[1..n]$, every set of positions $I\subseteq[1..n]$ and every integer $\tau\in[1..\lfloor n/2\rfloor]$ there is an $I$-local $\tau$-synchronizing set $\mathsf S$ of $T$ with
--   $$|\mathsf S|\le C\,|I|.$$
--   This localizes the synchronizing sets of Kempa and Kociumaka [KK19b] to the neighbourhood $\mathrm{Close}_\tau(I)$ of $I$; the proof of Lemma 1.2 uses it with $I=Z$, the phrase starts of $\mathrm{LZ77}(S)$.
--
--   Differences from the source:
--   - encoding: |S| ∈ O(|I|) → ∃ C (fixed before the alphabet, T, I and τ) with |S| ≤ C·|I|; reason: the O(·) constant is universal
--   - encoding: a set S of indices → a finite set of natural numbers; reason: only positions in [1..n] are constrained, and |S| = O(|I|) makes it finite
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…), p. 48 (PDF 50), Lemma 8.4

import Mathlib
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

/-- **Lemma 8.4** (p. 48). There is a universal constant `C` such that for every string
`T[1..n]`, every `I ⊆ [1..n]` and every `τ ∈ [1..⌊n/2⌋]` there is an `I`-local
`τ`-synchronizing set `S` of `T` with `|S| ≤ C·|I|`. -/
theorem lemma_8_4 : ∃ C : ℝ, ∀ {α : Type} [DecidableEq α] (T : List α) (I : Finset ℕ) (τ : ℕ),
    I ⊆ Finset.Icc 1 T.length → 1 ≤ τ → τ ≤ T.length / 2 →
      ∃ Sy : Finset ℕ, IsLocalSyncSet T I τ Sy ∧ (Sy.card : ℝ) ≤ C * (I.card : ℝ) := by sorry

end DynLZ77.Main
