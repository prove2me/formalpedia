-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_exists_open_eventual_uniform_of_equiLipschitz
-- name    : Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.exists_open_eventual_uniform_of_equiLipschitz
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:12.329469+00:00
-- url     : https://prove2.me/theorems/12cd5ecb-9cd5-4466-9898-4523dcd637df
-- title:
--   Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.exists_open_eventual_uniform_of_equiLipschitz
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
open Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics BergmanMonomials LatticeAsymptotics LaurentJetSeparatedness
open GlobalBergmanKernelBound MomentMinimizer MomentOptimizer MomentTargetGeodesic
open MomentFirstVariation MomentRegularity BergmanJetBasis MomentWeakGlobalKernel
open BergmanJetPointwiseLogKernel
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.exists_open_eventual_uniform_of_equiLipschitz
    {X : Type*} [PseudoMetricSpace X]
    (f : ℕ → X → ℝ) (g : X → ℝ)
    (C : ℝ≥0)
    (hf : ∀ᶠ k : ℕ in atTop, LipschitzWith C (f k))
    (hg : LipschitzWith C g)
    (x : X)
    (hx : Tendsto (fun k : ℕ => f k x) atTop (𝓝 (g x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ᶠ k : ℕ in atTop, ∀ y ∈ U,
        dist (f k y) (g y) < ε := by sorry
