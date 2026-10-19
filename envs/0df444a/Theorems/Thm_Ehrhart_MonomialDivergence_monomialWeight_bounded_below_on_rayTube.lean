-- Prove2me | Theorems.Thm_Ehrhart_MonomialDivergence_monomialWeight_bounded_below_on_rayTube
-- name    : Ehrhart.MonomialDivergence.monomialWeight_bounded_below_on_rayTube
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:44.97552+00:00
-- url     : https://prove2.me/theorems/7dc99051-ce63-4cd4-b8d8-5019f7b2766b
-- title:
--   Ehrhart.MonomialDivergence.monomialWeight_bounded_below_on_rayTube
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

theorem Ehrhart.MonomialDivergence.monomialWeight_bounded_below_on_rayTube {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    (hnonempty : K.Nonempty)
    {u v : Space n}
    (hseparate : ∀ y ∈ K,
      SupportFunction.pairing y v ≤
        SupportFunction.pairing u v)
    {φ : Space n → ℝ} {C : ℝ}
    (hupper : ∀ x : Space n,
      φ x ≤ SupportFunction.supportFunction K x + C)
    {k : ℝ} (hk : 0 < k) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ rayTube v,
      c ≤ MonomialIntegrability.monomialWeight k u φ x := by sorry
