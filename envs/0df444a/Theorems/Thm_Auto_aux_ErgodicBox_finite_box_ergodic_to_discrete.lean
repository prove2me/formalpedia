-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_finite_box_ergodic_to_discrete
-- name    : Auto.aux_ErgodicBox.finite_box_ergodic_to_discrete
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:44:38.823998+00:00
-- url     : https://prove2.me/theorems/615c54a6-7d92-4e8a-866e-9ed21bde7e36
-- title:
--   aux Ergodic Box: finite box ergodic to discrete
-- statement:
--   Generic finite-box ergodic-to-discrete transfer.  The input `hpoint` is
--   the local discrete-energy lower bound, `hdiscrete` is the discrete estimate,
--   and `hright` is the finite-box Hölder estimate for its norm product.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2754-L2774
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2754-L2774

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

theorem Auto.aux_ErgodicBox.finite_box_ergodic_to_discrete
    {X κ : Type*} [MeasurableSpace X] {μ : Measure X}
    (B B' : Finset κ) (T : κ → X → X)
    (hT : ∀ k ∈ B, MeasurePreserving (T k) μ μ)
    {J : ℕ} (d : Fin J → X → ℝ)
    (hd : ∀ j, AEStronglyMeasurable (d j) μ)
    (A P : ℝ≥0∞) (D Q : X → ℝ≥0∞)
    (hpoint : ∀ x, ∑ j : Fin J, ∑ k ∈ B,
      ‖d j (T k x)‖ₑ ^ (2 : ℕ) ≤ D x)
    (hdiscrete : ∀ x, D x ≤ A * Q x)
    (hQmeas : AEMeasurable Q μ)
    (hright : ∫⁻ x, Q x ∂μ ≤ (B'.card : ℝ≥0∞) * P) :
    (B.card : ℝ≥0∞) * ∑ j : Fin J, eLpNorm (d j) 2 μ ^ 2 ≤
      A * ((B'.card : ℝ≥0∞) * P) := by sorry
