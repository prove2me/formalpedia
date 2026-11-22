-- Prove2me | Theorems.Thm_CriticalPortraits_beta_unlinked
-- name    : CriticalPortraits.beta_unlinked
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:29.092652+00:00
-- url     : https://prove2.me/theorems/e4275520-769f-4e74-8798-0d2768b8e005
-- title:
--   Critical Portraits: beta unlinked
-- statement:
--   **Unlinked (N).** Distinct blocks of `β U` are unlinked.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1467-L1522
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1467-L1522

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.beta_unlinked {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcanon : LevelCanonical d m U) :
    ∀ A ∈ beta U, ∀ B ∈ beta U, A ≠ B → Unlinked A B := by sorry
