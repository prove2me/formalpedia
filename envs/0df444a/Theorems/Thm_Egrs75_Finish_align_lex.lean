-- Prove2me | Theorems.Thm_Egrs75_Finish_align_lex
-- name    : Egrs75.Finish.align_lex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:25.734101+00:00
-- url     : https://prove2.me/theorems/e3cb57ef-ccd8-42ec-8cb3-2161570f3c4a
-- title:
--   Finish: align lex
-- statement:
--   **Reduction (FULLY KERNEL-CLEAN).**  The lex repair step is taken as an EXPLICIT
--   hypothesis `hrepair_lex`.  From a `LowDigits p` seed strictly above `N`, repeatedly
--   applying it drives the base-`q` bitmask `badPrefix` to `0`, yielding a number that is
--   `> N`, `LowDigits p`, and `LowDigits q`.  Strong induction on `badPrefix q` of the
--   running number; the magnitude invariant `N < n` is carried (both repair branches keep
--   the number above `N`, so it is threaded directly rather than via `n < n'`).
--
--   KERNEL-CLEAN (no `sorry`, no axioms beyond propext/Classical.choice/Quot.sound).
--
--   The repair hypothesis `hrepair_lex` is given the running magnitude `N < n` (the
--   induction carries it as an invariant and threads it in), so the EGRS step's `N < n'`
--   guarantee — needed to keep the result above the floor — is honored at every step.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L230-L251
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L230-L251

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_Egrs75_ClearingHigh
public import Definitions.Def_LeanPool_Egrs75_MuFinish
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Totient
public import Definitions.Def_LeanPool_Egrs75_BadPrefixRoute
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.Finish
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.Probe

theorem Egrs75.Finish.align_lex {p q : ℕ} (N : ℕ)
    (hrepair_lex : ∀ {n : ℕ}, LowDigits p n → N < n → 0 < badCountQ q n →
      ∃ n', LowDigits p n' ∧ N < n' ∧ badPrefix q n' < badPrefix q n)
    (seed : ℕ) (hseedN : N < seed) (hseedp : LowDigits p seed) :
    ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by sorry
