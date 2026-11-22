-- Prove2me | Theorems.Thm_CriticalPortraits_betaK_ge
-- name    : CriticalPortraits.betaK_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:16.581397+00:00
-- url     : https://prove2.me/theorems/03eb8be0-1556-4915-b004-c618bef386f6
-- title:
--   Critical Portraits: beta K ge
-- statement:
--   Any balance index `≤ betaK`: `betaK` is the *largest* zero of the deficiency.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L938-L942
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L938-L942

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

theorem CriticalPortraits.betaK_ge {d m : ℕ} {U : Finset (ZMod (d * m))} {s : ZMod (d * m)} {k : ℕ}
    (hk : Defc U (s.val % m) (s.val / m) s.val k = 0) (hkle : k ≤ s.val / m - 1) :
    k ≤ betaK U s := by sorry
