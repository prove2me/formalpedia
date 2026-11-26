-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_eLpNorm_sq_eq_lintegral_rpow
-- name    : Auto.aux_ErgodicBox.eLpNorm_sq_eq_lintegral_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:44:05.464891+00:00
-- url     : https://prove2.me/theorems/49203b67-6493-5780-9c1a-ec5467d89cb6
-- title:
--   aux Ergodic Box: e Lp Norm sq eq lintegral rpow
-- statement:
--   The aux Ergodic Box construction uses the e Lp Norm sq eq lintegral rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2550-L2560
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2550-L2560

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem Auto.aux_ErgodicBox.eLpNorm_sq_eq_lintegral_rpow
    {X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [ENorm E]
    (μ : Measure X) (F : X → E) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm F p μ ^ 2 =
      (∫⁻ x, ‖F x‖ₑ ^ p.toReal ∂μ) ^ (2 / p.toReal) := by sorry
