-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_runFrom_take_periodic
-- name    : DeciSigma1.Arithmetic.runFrom_take_periodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:42.118623+00:00
-- url     : https://prove2.me/theorems/f4eab546-248e-4287-a8af-9f71866365d3
-- title:
--   Arithmetic: run From take periodic
-- statement:
--   Along a finite word of period `d`, the states of a run at cuts of at least `|S| · d` repeat
--   with period `d · |S|!`, as long as the cuts stay inside the word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L327-L350
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L327-L350

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Mathlib.Order.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
variable {β : Type*}
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Arithmetic.runFrom_take_periodic [Fintype S] (T : Table α S k) (q : S) {u : List α} {d o : ℕ}
    (hd : 0 < d) (hper : Words.PeriodicOn u d 0 u.length) (ho : Fintype.card S * d ≤ o) (m : ℕ)
    (hlen : o + m * (d * (Fintype.card S).factorial) ≤ u.length) :
    runFrom T.step q (u.take (o + m * (d * (Fintype.card S).factorial))) =
      runFrom T.step q (u.take o) := by sorry
