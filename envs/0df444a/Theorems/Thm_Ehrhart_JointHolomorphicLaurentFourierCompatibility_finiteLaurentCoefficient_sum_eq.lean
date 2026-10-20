-- Prove2me | Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_finiteLaurentCoefficient_sum_eq
-- name    : Ehrhart.JointHolomorphicLaurentFourierCompatibility.finiteLaurentCoefficient_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:49.881935+00:00
-- url     : https://prove2.me/theorems/98a38e67-7c45-4d3e-a162-73e98effa03c
-- title:
--   Ehrhart.JointHolomorphicLaurentFourierCompatibility.finiteLaurentCoefficient_sum_eq
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
open Ehrhart.JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13915
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13918

theorem Ehrhart.JointHolomorphicLaurentFourierCompatibility.finiteLaurentCoefficient_sum_eq
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hrepresentative :
      (fun z : WeightedTorusHilbert.LogTorus n => f z)
        =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ]
      (fun z => coverRepresentative F z.1 z.2))
    [Fintype (LatticeAsymptotics.monomialIndex K k)]
    (m : Fin n → ℤ) (x : Space n) :
    (∑ u : LatticeAsymptotics.monomialIndex K k,
      laurentCoefficient F
          (WeightedTorusHilbert.integerExponent K hk u) *
        (if m = WeightedTorusHilbert.integerExponent K hk u
          then WeightedTorusHilbert.radialCharacter
            (WeightedTorusHilbert.integerExponent K hk u) x
          else 0)) =
      laurentCoefficient F m *
        WeightedTorusHilbert.radialCharacter m x := by sorry
