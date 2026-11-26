-- Prove2me | Theorems.Thm_Auto_aux_orbit_measurePreserving
-- name    : Auto.aux_orbit_measurePreserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:36:21.299856+00:00
-- url     : https://prove2.me/theorems/1a70a391-4101-467b-b8ec-2009b0fac28b
-- title:
--   Auto: aux orbit measure Preserving
-- statement:
--   A joint orbit preserves the measure when each generator does.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L107-L119
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L107-L119

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

theorem Auto.aux_orbit_measurePreserving {X : Type*} [MeasurableSpace X]
    {μ : Measure X} : ∀ {n : ℕ} (S : Fin n → X → X) (k : Fin n → ℕ),
      (∀ i, MeasurePreserving (S i) μ μ) →
      MeasurePreserving (aux_orbit S k) μ μ
  := by sorry
