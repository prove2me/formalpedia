-- Prove2me | Theorems.Thm_Auto_aux_restrict_logarithmicMeasure_Ioc
-- name    : Auto.aux_restrict_logarithmicMeasure_Ioc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:23.735147+00:00
-- url     : https://prove2.me/theorems/dc92420c-c093-497c-aa98-36a02dd3cdbb
-- title:
--   Auto: aux restrict logarithmic Measure Ioc
-- statement:
--   Restricting the logarithmic measure to a contained open-closed interval.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L990-L995
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L990-L995

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_restrict_logarithmicMeasure_Ioc {α β x y : ℝ}
    (hsub : Set.Ioc x y ⊆ Set.Icc α β) :
    (aux_logarithmicMeasure α β).restrict (Set.Ioc x y) =
      (volume.restrict (Set.Ioc x y)).withDensity fun t ↦ ENNReal.ofReal t⁻¹ := by sorry
