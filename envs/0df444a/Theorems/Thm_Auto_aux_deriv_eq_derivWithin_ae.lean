-- Prove2me | Theorems.Thm_Auto_aux_deriv_eq_derivWithin_ae
-- name    : Auto.aux_deriv_eq_derivWithin_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:38.096804+00:00
-- url     : https://prove2.me/theorems/a126b224-870d-596e-9782-3a7e8764d4ee
-- title:
--   Auto: aux deriv eq deriv Within ae
-- statement:
--   On the interior of the ambient interval, ordinary and interval derivatives
--   agree almost everywhere for the logarithmic measure.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L619-L625
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L619-L625

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_deriv_eq_derivWithin_ae {α β : ℝ} (a : ℝ → ℝ) :
    deriv a =ᵐ[aux_logarithmicMeasure α β] derivWithin a (Set.Icc α β) := by sorry
