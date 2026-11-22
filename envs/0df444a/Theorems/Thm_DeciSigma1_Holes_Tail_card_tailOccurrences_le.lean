-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_card_tailOccurrences_le
-- name    : DeciSigma1.Holes.Tail.card_tailOccurrences_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:46.721284+00:00
-- url     : https://prove2.me/theorems/b6fa1001-30a7-44cf-a8bf-7f1f5782a8d5
-- title:
--   Tail: card tail Occurrences le
-- statement:
--   If the rejected tail `[J, |w|)` of `w` has a periodic cover by at most `P` factors of period
--   at most `E` with at most `T` uncovered positions, the longest suffix of `w` with period at most
--   `E` is shorter than `Y`, and `b ≥ 1 + T + P (Y + T + 2 E P + 1)`, then at most `P` occurrences of
--   the suffix of length `b` of `w` start at or after `J`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/WindowChains.lean#L101-L232
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/WindowChains.lean#L101-L232

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α]

theorem DeciSigma1.Holes.Tail.card_tailOccurrences_le {w : List α} {J P E T Y b : ℕ} (hcov : PeriodicCover w J P E T)
    (hY : longestPeriodicSuffixLength E w < Y) (hb : 1 + T + P * (Y + T + 2 * E * P + 1) ≤ b) :
    ((occurrences w w b).filter (fun e => J + b ≤ e)).card ≤ P := by sorry
