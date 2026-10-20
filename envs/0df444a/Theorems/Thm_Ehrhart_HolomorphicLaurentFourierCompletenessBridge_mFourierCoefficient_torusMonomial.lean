-- Prove2me | Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_mFourierCoefficient_torusMonomial
-- name    : Ehrhart.HolomorphicLaurentFourierCompletenessBridge.mFourierCoefficient_torusMonomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:48.222718+00:00
-- url     : https://prove2.me/theorems/6553f35a-d821-4d42-a38e-e6ad7eb4201d
-- title:
--   Ehrhart.HolomorphicLaurentFourierCompletenessBridge.mFourierCoefficient_torusMonomial
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
open Ehrhart.HolomorphicLaurentFourierCompletenessBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.HolomorphicLaurentFourierCompletenessBridge._p2m_local_instance_3610026555_13449
attribute [local instance] Ehrhart.HolomorphicLaurentFourierCompletenessBridge._p2m_local_instance_3610026555_13452

theorem Ehrhart.HolomorphicLaurentFourierCompletenessBridge.mFourierCoefficient_torusMonomial {n : ℕ}
    (m q : Fin n → ℤ) (x : Space n) :
    UnitAddTorus.mFourierCoeff
      (fun θ : TorusCharacters.AngularTorus n =>
        WeightedTorusHilbert.torusMonomial q (x, θ)) m =
      if m = q then
        WeightedTorusHilbert.radialCharacter q x
      else 0 := by sorry
