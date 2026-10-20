-- Prove2me | Theorems.Thm_Ehrhart_GenuineJetAdaptedBasisCounting_span_adaptedIndices_eq
-- name    : Ehrhart.GenuineJetAdaptedBasisCounting.span_adaptedIndices_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:44.97552+00:00
-- url     : https://prove2.me/theorems/c4c21eb0-c1a2-48ec-a4b0-92b62466cfbd
-- title:
--   Ehrhart.GenuineJetAdaptedBasisCounting.span_adaptedIndices_eq
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
open Ehrhart.GenuineJetAdaptedBasisCounting
open Set Module
open scoped BigOperators InnerProductSpace

theorem Ehrhart.GenuineJetAdaptedBasisCounting.span_adaptedIndices_eq {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (b : OrthonormalBasis ι ℂ V) (S : Submodule ℂ V)
    (hb : ∀ i, b i ∈ S ∨ b i ∈ Sᗮ) :
    Submodule.span ℂ
      (Set.range (fun i : adaptedIndices b S => b (i : ι))) = S := by sorry
