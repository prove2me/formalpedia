-- Prove2me | Theorems.Thm_Auto_aux_continuousLinearMap_pi_injective_of_iInf_ker_eq_bot
-- name    : Auto.aux_continuousLinearMap_pi_injective_of_iInf_ker_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:46:15.899168+00:00
-- url     : https://prove2.me/theorems/ca6325cc-fbca-55f7-8673-b41a65417bef
-- title:
--   Auto: aux continuous Linear Map pi injective of i Inf ker eq bot
-- statement:
--   The kernel condition in the Brascamp--Lieb corollary says precisely that the combined
--   coordinate map is injective.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2674-L2689
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2674-L2689

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_continuousLinearMap_pi_injective_of_iInf_ker_eq_bot
    {ι : Type*} {m l : ℕ} {d : ι → ℕ}
    (pi : ∀ i, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin (d i)))
    (hker : ⨅ i, LinearMap.ker (pi i).toLinearMap = ⊥) :
    Function.Injective (ContinuousLinearMap.pi pi) := by sorry
