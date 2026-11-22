-- Prove2me | Theorems.Thm_CriticalPortraits_N0
-- name    : CriticalPortraits.N0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:20.123668+00:00
-- url     : https://prove2.me/theorems/16ecdf60-fed2-4555-bdec-647a577760cb
-- title:
--   Critical Portraits: N0
-- statement:
--   **N0.** No survivor lies strictly inside one column-window above an edge bottom:
--       there is no `t ∈ U` with `v*(u) < t.val < v*(u) + m`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1010-L1041
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1010-L1041

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

theorem CriticalPortraits.N0 {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m)
    {t : ZMod (d * m)} (htU : t ∈ U)
    (hlo : (betaParent U u).val < t.val) (hhi : t.val < (betaParent U u).val + m) : False := by sorry
