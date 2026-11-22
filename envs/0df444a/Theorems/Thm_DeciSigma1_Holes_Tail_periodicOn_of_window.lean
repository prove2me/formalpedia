-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_periodicOn_of_window
-- name    : DeciSigma1.Holes.Tail.periodicOn_of_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:23.789952+00:00
-- url     : https://prove2.me/theorems/89fb3a90-4a46-4a65-b35a-0fd04c2c1782
-- title:
--   Tail: periodic On of window
-- statement:
--   If an interval `[s, e)` has period `p` and contains an interval `[a, b)` of length at least
--   `p + g` with period `g`, then the whole interval `[s, e)` has period `g`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L566-L583
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L566-L583

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.periodicOn_of_window {w : List α} {p g s e a b : ℕ} (hp : PeriodicOn w p s e)
    (hg : PeriodicOn w g a b)
    (hsa : s ≤ a) (hbe : b ≤ e) (hlen : a + p + g ≤ b) (hp0 : 0 < p) : PeriodicOn w g s e := by sorry
