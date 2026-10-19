-- Prove2me | Theorems.Thm_Ehrhart_MomentInteriorLegendre_locallyLipschitzOn_finiteEnergySourceLegendre_interior
-- name    : Ehrhart.MomentInteriorLegendre.locallyLipschitzOn_finiteEnergySourceLegendre_interior
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/d4f18e62-61eb-4fc8-841a-29871efd4b6a
-- title:
--   Ehrhart.MomentInteriorLegendre.locallyLipschitzOn_finiteEnergySourceLegendre_interior
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
open Ehrhart.MomentInteriorLegendre
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentFunctionalCoercivity MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentMonotoneTransport
open scoped BigOperators ENNReal Topology

theorem Ehrhart.MomentInteriorLegendre.locallyLipschitzOn_finiteEnergySourceLegendre_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    LocallyLipschitzOn (interior K.carrier)
      (legendreTransform F.potential) := by sorry
