-- Prove2me | Theorems.Thm_Auto_aux_crossIndices_b_injective
-- name    : Auto.aux_crossIndices_b_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:23.758443+00:00
-- url     : https://prove2.me/theorems/44d36d24-c991-419a-ba11-b90da14f14f9
-- title:
--   Auto: aux cross Indices b injective
-- statement:
--   A monotone label sequence leaves every occupied dyadic interval at most once.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L286-L302
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L286-L302

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_crossIndices_b_injective {J : ℕ} {b : Fin (J + 1) → ℤ}
    (hb : Monotone b) :
    Function.Injective (fun j : aux_crossIndices b ↦ b j.1.castSucc) := by sorry
