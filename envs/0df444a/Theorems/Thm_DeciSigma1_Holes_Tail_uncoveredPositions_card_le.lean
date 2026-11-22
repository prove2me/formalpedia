-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_uncoveredPositions_card_le
-- name    : DeciSigma1.Holes.Tail.uncoveredPositions_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:06.488777+00:00
-- url     : https://prove2.me/theorems/0183b332-5987-423f-920f-ec9e67e1f593
-- title:
--   Tail: uncovered Positions card le
-- statement:
--   If each of `n` consecutive segments of `T` positions from `J` contains a covered position
--   below `len`, and `len ≤ J + n T + T`, at most `(|fs| + 1) · 2T` positions of `[J, len)` are
--   uncovered: an uncovered position before the last full segment is charged to the start of the
--   next factor, at distance at most `2T`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L511-L558
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L511-L558

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.uncoveredPositions_card_le (fs : List PeriodicFactor) {J T n len : ℕ} (hT : 0 < T)
    (hlen : len ≤ J + n * T + T)
    (hcov : ∀ m < n, ∃ y, J + m * T ≤ y ∧ y < J + m * T + T ∧ y < len ∧ Covers fs y) :
    (uncoveredPositions fs J len).card ≤ (fs.length + 1) * (2 * T) := by sorry
