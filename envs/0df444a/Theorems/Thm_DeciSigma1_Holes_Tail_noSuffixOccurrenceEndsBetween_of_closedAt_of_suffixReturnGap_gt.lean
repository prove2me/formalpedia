-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_noSuffixOccurrenceEndsBetween_of_closedAt_of_suffixReturnGap_gt
-- name    : DeciSigma1.Holes.Tail.noSuffixOccurrenceEndsBetween_of_closedAt_of_suffixReturnGap_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:09:43.364304+00:00
-- url     : https://prove2.me/theorems/d5a478ea-251a-4747-bb35-de48c288b648
-- title:
--   Tail: no Suffix Occurrence Ends Between of closed At of suffix Return Gap gt
-- statement:
--   If `x[c, c')`, with `h = c' - c`, is closed at a window `B' ≥ B + h` and
--   `suffixReturnGap t B > h`, then no occurrence of the suffix of length `B'` of `t` ends in
--   `(c, c']`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L715-L751
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L715-L751

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.noSuffixOccurrenceEndsBetween_of_closedAt_of_suffixReturnGap_gt [DecidableEq α]
    {T : Table α S k} {q0 : S}
    {x t : List α} {B B' c c' : ℕ}
    (hcl : ClosedAt T q0 x B' c c') (hB : B + (c' - c) ≤ B')
    (hD : ∀ h,
        Words.suffixReturnGap t B = some h → c' - c <
            h) : NoSuffixOccurrenceEndsBetween x t B' c c' := by sorry
