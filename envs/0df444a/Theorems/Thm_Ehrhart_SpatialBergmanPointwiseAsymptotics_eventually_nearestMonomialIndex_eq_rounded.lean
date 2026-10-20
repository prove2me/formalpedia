-- Prove2me | Theorems.Thm_Ehrhart_SpatialBergmanPointwiseAsymptotics_eventually_nearestMonomialIndex_eq_rounded
-- name    : Ehrhart.SpatialBergmanPointwiseAsymptotics.eventually_nearestMonomialIndex_eq_rounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/6671ed30-f535-4e8c-b97b-40984eca6703
-- title:
--   Ehrhart.SpatialBergmanPointwiseAsymptotics.eventually_nearestMonomialIndex_eq_rounded
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
open Ehrhart.SpatialBergmanPointwiseAsymptotics
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
open TranslatedGaussianLatticeAsymptotics

theorem Ehrhart.SpatialBergmanPointwiseAsymptotics.eventually_nearestMonomialIndex_eq_rounded {n : ℕ}
    (K : CenteredBody n)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    ∀ᶠ k : ℕ in atTop,
      (nearestMonomialIndex K u k : Space n) =
        roundedLatticeExponent k u := by sorry
