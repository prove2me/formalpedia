-- Prove2me | Theorems.Thm_Ehrhart_MonomialDivergence_supportFunction_le_pairing_add_on_rayTube
-- name    : Ehrhart.MonomialDivergence.supportFunction_le_pairing_add_on_rayTube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:44.97552+00:00
-- url     : https://prove2.me/theorems/bb9a1919-4a22-409c-b4a3-2d1de271f11a
-- title:
--   Ehrhart.MonomialDivergence.supportFunction_le_pairing_add_on_rayTube
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
open Ehrhart.MonomialDivergence
open Set MeasureTheory
open scoped BigOperators ENNReal

theorem Ehrhart.MonomialDivergence.supportFunction_le_pairing_add_on_rayTube {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    (hnonempty : K.Nonempty)
    {u v : Space n}
    (hseparate : ∀ y ∈ K,
      SupportFunction.pairing y v ≤
        SupportFunction.pairing u v) :
    ∃ D : ℝ, ∀ x ∈ rayTube v,
      SupportFunction.supportFunction K x ≤
        SupportFunction.pairing u x + D := by sorry
