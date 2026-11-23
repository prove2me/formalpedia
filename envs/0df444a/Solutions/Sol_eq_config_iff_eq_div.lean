-- Prove2me | solution 1 for eq_config_iff_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:49:15.547067+00:00
-- url     : https://prove2.me/submissions/318e3d41-c15b-4147-b4b1-c49503919d1f

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {q : G.V} (d : ℤ) (c₁ c₂ : Config G q) : c₁ = c₂ ↔ toDiv d c₁ = toDiv d c₂ := by
  constructor
  -- Forward direction is clear
  intro h_eq
  rw [h_eq]
  -- Reverse direction takes more
  intro h_eq
  apply congrFun at h_eq
  ext v
  specialize h_eq v
  dsimp only [toDiv, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul] at h_eq
  by_cases h_v : q = v
  . -- Case v = q
    rw [← h_v]
    rw [c₁.q_zero, c₂.q_zero]
  . -- Case v ≠ q
    simp only [ne_eq, h_v, not_false_eq_true, one_chip_apply_other, mul_zero, add_zero] at h_eq
    exact h_eq
