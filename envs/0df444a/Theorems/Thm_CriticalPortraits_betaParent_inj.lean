-- Prove2me | Theorems.Thm_CriticalPortraits_betaParent_inj
-- name    : CriticalPortraits.betaParent_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:00.909003+00:00
-- url     : https://prove2.me/theorems/e5802ac4-a47f-4251-be2c-1503f81bded2
-- title:
--   Critical Portraits: beta Parent inj
-- statement:
--   **Injectivity (I).** The parent map is injective on survivors of canonical `U`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L457-L532
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L457-L532

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

theorem CriticalPortraits.betaParent_inj {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u1 u2 : ZMod (d * m)} (hu1 : u1 ∈ U) (hu2 : u2 ∈ U)
    (heq : betaParent U u1 = betaParent U u2) : u1 = u2 := by sorry
