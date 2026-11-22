-- Prove2me | Theorems.Thm_Egrs75_MuFinish_align_mu
-- name    : Egrs75.MuFinish.align_mu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:15.744949+00:00
-- url     : https://prove2.me/theorems/d8991d1d-0511-4939-bbb3-ff602c901195
-- title:
--   Mu Finish: align mu
-- statement:
--   **ALIGN via the lex pair `(μ, n)` (KERNEL-CLEAN).**  Repeatedly applying the
--   single move from a seed whose floor block exceeds `N` yields a number that is
--   `> N`, `LowDigits p`, and `LowDigits q`.  Outer strong induction on `μ`, inner
--   on `n`; the floor invariant `N < (n/q^i)·q^i` is threaded (it implies `N < n`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MuFinish.lean#L284-L337
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MuFinish.lean#L284-L337

module
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
public import Definitions.Def_LeanPool_Egrs75_AddBranch
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SeedWindow
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Mathlib.Data.Nat.Totient
public import Definitions.Def_LeanPool_Egrs75_MuFinish
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MuFinish
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.P4

theorem Egrs75.MuFinish.align_mu {p q : ℕ} (hq3 : 3 ≤ q) (N : ℕ)
    (hmove : ∀ {n : ℕ}, LowDigits p n → ∀ (hbad : 0 < badCountQ q n),
        N < n / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad) →
        ∃ n', LowDigits p n' ∧
          N < n' / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad) ∧
          (muVal q hq3 n' < muVal q hq3 n ∨
            (muVal q hq3 n' = muVal q hq3 n ∧ n' < n)))
    (seed : ℕ) (hsN : N < seed) (hsp : LowDigits p seed)
    (hsfl : ∀ (hbad : 0 < badCountQ q seed),
        N < seed / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad)) :
    ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by sorry
