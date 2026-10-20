-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetDiagonalObservableLatticeIdentity_momentNormalizedLaurentObservable_eq_integral_normalizedMonomialDensity
-- name    : Ehrhart.BergmanJetDiagonalObservableLatticeIdentity.momentNormalizedLaurentObservable_eq_integral_normalizedMonomialDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:15.527216+00:00
-- url     : https://prove2.me/theorems/d8259a46-2d3d-47af-b5bb-60666a8c4db5
-- title:
--   Ehrhart.BergmanJetDiagonalObservableLatticeIdentity.momentNormalizedLaurentObservable_eq_integral_normalizedMonomialDensity
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
open Ehrhart.BergmanJetDiagonalObservableLatticeIdentity
open Set Function Filter MeasureTheory
open BergmanMonomials BergmanNormalization LatticeAsymptotics MonomialIntegrability MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergmanProbabilityEndpoint
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetDiagonalObservableLatticeIdentity.momentNormalizedLaurentObservable_eq_integral_normalizedMonomialDensity
    {n k : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (f : Space n → ℝ)
    (u : monomialIndex K k) :
    momentNormalizedLaurentObservable
        F k f (u : Space n) =
      ∫ x : Space n,
        f x * normalizedMonomialDensity
          K k (momentNormalizedPotential F) u x
        ∂(volume : Measure (Space n)) := by sorry
