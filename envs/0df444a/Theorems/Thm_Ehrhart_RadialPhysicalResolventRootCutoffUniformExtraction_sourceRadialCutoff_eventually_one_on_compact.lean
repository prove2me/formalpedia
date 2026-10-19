-- Prove2me | Theorems.Thm_Ehrhart_RadialPhysicalResolventRootCutoffUniformExtraction_sourceRadialCutoff_eventually_one_on_compact
-- name    : Ehrhart.RadialPhysicalResolventRootCutoffUniformExtraction.sourceRadialCutoff_eventually_one_on_compact
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/944b4241-864c-41d1-814c-c8a1d47932e3
-- title:
--   Ehrhart.RadialPhysicalResolventRootCutoffUniformExtraction.sourceRadialCutoff_eventually_one_on_compact
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
open Ehrhart.RadialPhysicalResolventRootCutoffUniformExtraction
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert WeightedResolventConstantCore MatrixTorusBochnerCoreDensity
open scoped BigOperators ENNReal InnerProductSpace Topology

theorem Ehrhart.RadialPhysicalResolventRootCutoffUniformExtraction.sourceRadialCutoff_eventually_one_on_compact
    {n : ℕ} {s : Set (LogTorus n)}
    (hs : IsCompact s) :
    ∀ᶠ m : ℕ in atTop,
      ∀ q ∈ s, sourceRadialCutoff m q = 1 := by sorry
