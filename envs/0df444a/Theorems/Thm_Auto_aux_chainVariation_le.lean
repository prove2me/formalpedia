-- Prove2me | Theorems.Thm_Auto_aux_chainVariation_le
-- name    : Auto.aux_chainVariation_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:15.263392+00:00
-- url     : https://prove2.me/theorems/1373b502-dc4c-574b-90ed-1002dc7d1f78
-- title:
--   Auto: aux chain Variation le
-- statement:
--   A single monotone chain is one candidate in the defining variation
--   supremum.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L80-L88
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L80-L88

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_chainVariation_le {B : Type*} [SeminormedAddCommGroup B]
    {I : Set ℝ} (a : I → B) (r : ℝ) (J : ℕ)
    (t : Fin (J + 1) → I) (ht : Monotone t) :
    (∑ j : Fin J,
      (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹ ≤
        finiteVariationSeminorm a r J := by sorry
