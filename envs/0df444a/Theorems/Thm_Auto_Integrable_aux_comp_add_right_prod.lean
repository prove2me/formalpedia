-- Prove2me | Theorems.Thm_Auto_Integrable_aux_comp_add_right_prod
-- name    : Auto.Integrable.aux_comp_add_right_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:45.662793+00:00
-- url     : https://prove2.me/theorems/18f49c25-12da-45e1-9c02-5907e3d00484
-- title:
--   Integrable: aux comp add right prod
-- statement:
--   Translation preserves integrability for the product Lebesgue measure.  The product type
--   does not expose the additive Haar invariance instance directly, so we obtain it from the two
--   coordinate translations.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1381-L1392
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1381-L1392

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.Integrable.aux_comp_add_right_prod {m l : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : Integrable f) (z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) :
    Integrable (fun x ↦ f (x + z)) := by sorry
