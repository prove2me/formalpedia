-- Prove2me | Theorems.Thm_CriticalPortraits_Defc_pos_after
-- name    : CriticalPortraits.Defc_pos_after
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:14.9609+00:00
-- url     : https://prove2.me/theorems/662df471-2844-4999-85f7-5baa66c0684d
-- title:
--   Critical Portraits: Defc pos after
-- statement:
--   **M2 strict positivity.** For a survivor `u` of canonical `U` and `betaK U u < j ≤ lu-1`,
--       the deficiency at `j` is strictly positive.  If it were `≤ 0`, then since `D(lu-1) ≥ 0` (E1)
--       and up-steps are `≤ 1`, the discrete IVT on `[j, lu-1]` yields an exact zero `> K`,
--       contradicting maximality `betaK_max`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L903-L933
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L903-L933

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

theorem CriticalPortraits.Defc_pos_after {d m : ℕ} (_hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (_hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (_hu : u ∈ U) (hlu : 1 ≤ u.val / m) {j : ℕ}
    (hj1 : betaK U u < j) (hj2 : j ≤ u.val / m - 1) :
    0 < Defc U (u.val % m) (u.val / m) u.val j := by sorry
