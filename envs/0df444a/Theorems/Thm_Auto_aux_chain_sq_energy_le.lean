-- Prove2me | Theorems.Thm_Auto_aux_chain_sq_energy_le
-- name    : Auto.aux_chain_sq_energy_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:39:54.359032+00:00
-- url     : https://prove2.me/theorems/deb09c8b-0f70-585e-980d-b2a5aaff2846
-- title:
--   Auto: aux chain sq energy le
-- statement:
--   Summing the first FTC estimate over a monotone finite chain.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L763-L799
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L763-L799

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_chain_sq_energy_le {J : ℕ} {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (t : Fin (J + 1) → Set.Icc α β) (ht : Monotone t) :
    (∑ j : Fin J, ‖a (t j.succ) - a (t j.castSucc)‖ₑ ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((β - α) / α) *
        ∫⁻ x in Set.Icc α β, ‖x * deriv a x‖ₑ ^ (2 : ℝ)
          ∂aux_logarithmicMeasure α β := by sorry
