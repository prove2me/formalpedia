-- Prove2me | Theorems.Thm_DynStrings_corollary_4_8_unimodal_blocks
-- name    : DynStrings.corollary_4_8_unimodal_blocks
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:29.379658+00:00
-- url     : https://prove2.me/theorems/9d9febb4-4d52-4e09-8026-c6b22402cc59
-- title:
--   Corollary 4.8 — no two adjacent equal active symbols, and every block of round $k+1$ is unimodal
-- statement:
--   Let $k\ge1$ be odd, let $S$ be a string, and fix any choice of the orders.
--
--   1. No two adjacent symbols of $S_k$ are equal and active in round $k+1$.
--   2. Every block formed from $S_k$ in round $k+1$ is unimodal: its symbols are distinct from their neighbours, and they strictly increase with respect to $\prec_{k+1}$ up to some position and strictly decrease afterwards (either part may consist of one symbol).
--
--   Long blocks therefore contain long monotone sequences in the random order $\prec_{k+1}$, which is what makes them rare.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet $\Sigma$ → strings over an arbitrary type $\alpha$ with decidable equality; reason: the statement holds for every alphabet type, and a countably infinite $\alpha$ gives the source's statement
--   - encoding: every choice of the orders → every family `lt` with `IsOrderFamily lt` (strict total orders on all syntactic symbols for even k ≥ 2, paused before active); reason: the parse reads only well-formed symbols, so orders on the larger syntactic type restrict to exactly the source's orders
--   - encoding: 1-based symbol positions S_k[i] → 0-based list indices of the level word; reason: index shift only; every inequality is shifted accordingly
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Corollary 4.8, p.17

import Mathlib
import Definitions.Def_DynStrings_Parse

namespace DynStrings

/-- **Corollary 4.8**, p.17.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

Let `k ≥ 1` be odd, `S` a string, and fix a choice of the orders.
(a) No two adjacent symbols of `S_k` are equal and active in round `k + 1`.
(b) Every block formed in round `k + 1` is unimodal: its symbols are distinct from their
neighbours, and they strictly increase with respect to `≺_{k+1}` up to some position and strictly
decrease afterwards.

**Formalization Note.** Blocks are the index intervals `[a, b)` of `S_k` (0-based) produced by
block round `k + 1`; the peak is the index `t ∈ [a, b)`. -/
theorem corollary_4_8_unimodal_blocks {α : Type} [DecidableEq α] (S : List α)
    (lt : ℕ → StrSym α → StrSym α → Prop) (hlt : IsOrderFamily lt) (k : ℕ) (hk : Odd k) :
    (∀ j (A B : StrSym α), (level lt S k)[j]? = some A → (level lt S k)[j + 1]? = some B →
      ¬ (A = B ∧ Active (k + 1) A)) ∧
    (∀ p ∈ blockIntervals lt (k + 1) (level lt S k),
      (∀ j (A B : StrSym α), p.1 ≤ j → j + 1 < p.2 → (level lt S k)[j]? = some A →
        (level lt S k)[j + 1]? = some B → A ≠ B) ∧
      ∃ t, p.1 ≤ t ∧ t < p.2 ∧
        (∀ j (A B : StrSym α), p.1 ≤ j → j < t → (level lt S k)[j]? = some A →
          (level lt S k)[j + 1]? = some B → lt (k + 1) A B) ∧
        (∀ j (A B : StrSym α), t ≤ j → j + 1 < p.2 → (level lt S k)[j]? = some A →
          (level lt S k)[j + 1]? = some B → lt (k + 1) B A)) := by sorry

end DynStrings
