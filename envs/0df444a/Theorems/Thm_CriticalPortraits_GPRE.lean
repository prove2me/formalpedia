-- Prove2me | Theorems.Thm_CriticalPortraits_GPRE
-- name    : CriticalPortraits.GPRE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:38.79316+00:00
-- url     : https://prove2.me/theorems/114fa828-7f84-48bb-b8bc-f35f26c12b1a
-- title:
--   Critical Portraits: GPRE
-- statement:
--   **GPRE prefix bound.** For a survivor `u` of canonical `U`, with `K := betaK U u` and a
--       `φ`-column index `j` with `K < j ≤ lu`, the survivor count from `v*(u)` up to the `φ`-point at
--       level `j` is at most `j - K - 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L966-L1006
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L966-L1006

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

theorem CriticalPortraits.GPRE {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m) {j : ℕ}
    (hj1 : betaK U u < j) (hj2 : j ≤ u.val / m) :
    (Scount U (betaParent U u).val (u.val % m + j * m) : ℤ) ≤ (j : ℤ) - (betaK U u : ℤ) - 1 := by sorry
