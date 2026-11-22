-- Prove2me | Theorems.Thm_CriticalPortraits_spanning_edge
-- name    : CriticalPortraits.spanning_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:50.250759+00:00
-- url     : https://prove2.me/theorems/8b4729d1-fc3d-43f7-add0-ee4fdf073e9b
-- title:
--   Critical Portraits: spanning edge
-- statement:
--   **The spanning-edge kernel.**  In one portrait `P`, for a survivor `x` and a level `ℓ`
--       strictly inside `x`'s own window `(loV P x, hiV x)`, there is a survivor `b` of a different
--       column than `x` whose edge **straddles** the value `colV x + ℓ * m`:
--       `(predIn P b _).val < colV x + ℓ*m < b.val < x.val`.
--
--       This is the formalized **Structural Lemma / Bridge** content: the value `v₀ = colV x + ℓ*m`
--       (a same-fiber position strictly inside `x`'s edge) is crossed by some maximal nested tile of a
--       different column.  Proved from saturation (`edge_tight_geom`), column-separation
--       (`column_sep_geom`), and the gap/cover/seam machinery.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L695-L767
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L695-L767

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.spanning_edge [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) {x : ZMod (d * m)} (hx : x ∈ T P)
    {ℓ : ℕ} (hℓ1 : loV P x < ℓ) (hℓ2 : ℓ < hiV x) :
    ∃ b, ∃ hb : b ∈ T P, colV b ≠ colV x ∧
      (predIn P b hb).val < colV x + ℓ * m ∧ colV x + ℓ * m < b.val ∧ b.val < x.val := by sorry
