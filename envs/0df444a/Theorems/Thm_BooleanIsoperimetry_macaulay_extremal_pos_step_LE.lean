-- Prove2me | Theorems.Thm_BooleanIsoperimetry_macaulay_extremal_pos_step_LE
-- name    : BooleanIsoperimetry.macaulay_extremal_pos_step_LE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:56.666427+00:00
-- url     : https://prove2.me/theorems/361c403a-2c19-4cfd-b6c3-8dc8d0fb2640
-- title:
--   Boolean Isoperimetry: macaulay extremal pos step LE
-- statement:
--   **Positive-cascade Case-I (LE) Macaulay shadow-sum leaf.**  Now a *proved*
--   corollary of the set-family shadow leaf `H_shadow_LE_sum` (which collapses the
--   Frankl–Füredi paired-compression cost via `H_exchange_max_form_pos`).  The
--   hypotheses `ih`, `hp`, `hq`, `hpq` are retained to keep the call site signature
--   stable; the content is entirely the shadow-sum comparison.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L70-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L70-L78

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_MacaulayMin
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.macaulay_extremal_pos_step_LE (n : ℕ)
    (_ : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (_ : p ≤ 2 ^ n) (_ : q ≤ 2 ^ n)
    (_ : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) (hq_pos : 1 ≤ q)
    (hba : b ≤ a) (hcase : a ≤ H n b) :
    H n p + H n q ≤ H n a + H n b := by sorry
