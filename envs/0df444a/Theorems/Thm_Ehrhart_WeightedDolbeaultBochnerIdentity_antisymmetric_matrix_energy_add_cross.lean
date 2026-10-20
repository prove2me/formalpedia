-- Prove2me | Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_antisymmetric_matrix_energy_add_cross
-- name    : Ehrhart.WeightedDolbeaultBochnerIdentity.antisymmetric_matrix_energy_add_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/bd0e69fe-6baf-4cd4-a44c-bff1f01654cc
-- title:
--   Ehrhart.WeightedDolbeaultBochnerIdentity.antisymmetric_matrix_energy_add_cross
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | EhrhartVolumeInequality | external Lean 4.33.1 validation; bundle SHA256 7150ea60aef8441515028279454832b05d0f964f3966505d147b2c1d8afe9763

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedDolbeaultBochnerIdentity
open Set MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal ComplexConjugate

theorem Ehrhart.WeightedDolbeaultBochnerIdentity.antisymmetric_matrix_energy_add_cross {n : ℕ}
    (A : Fin n → Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n,
      (A i j - A j i) * conj (A i j - A j i)) / 2 +
      (∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A j i)) =
      ∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A i j) := by sorry
