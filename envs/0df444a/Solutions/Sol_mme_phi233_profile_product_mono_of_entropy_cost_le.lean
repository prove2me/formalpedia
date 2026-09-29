-- Prove2me | solution 1 for mme_phi233_profile_product_mono_of_entropy_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:22:20.523291+00:00
-- url     : https://prove2.me/submissions/9ae4a22c-b714-4989-a666-223a4013f2ec

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option warningAsError true

private theorem self_rpow_as_entropy_exp (x : ℝ) (hx : 0 ≤ x) :
    x ^ x = Real.exp (-Real.negMulLog x) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · rw [Real.rpow_def_of_pos hx]
    unfold Real.negMulLog
    congr 1
    ring

private theorem twice_self_rpow_as_entropy_exp (x : ℝ) (hx : 0 ≤ x) :
    x ^ (2 * x) = Real.exp (-2 * Real.negMulLog x) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · rw [Real.rpow_def_of_pos hx]
    unfold Real.negMulLog
    congr 1
    ring

private theorem phi233_profile_product_as_entropy_exp
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a ^ (2 * a) * b ^ b * c ^ c * d ^ d =
      Real.exp
        (-2 * Real.negMulLog a - Real.negMulLog b -
          Real.negMulLog c - Real.negMulLog d) := by
  rw [twice_self_rpow_as_entropy_exp a ha,
    self_rpow_as_entropy_exp b hb,
    self_rpow_as_entropy_exp c hc,
    self_rpow_as_entropy_exp d hd]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1

/-- Monotonicity bridge from the continuous logarithmic entropy cost to the
profile product occurring in the type-2 completion factor. -/
theorem solution
    (a b c d a' b' c' d' : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c') (hd' : 0 ≤ d')
    (hcost :
      -2 * Real.negMulLog a - Real.negMulLog b -
          Real.negMulLog c - Real.negMulLog d ≤
        -2 * Real.negMulLog a' - Real.negMulLog b' -
          Real.negMulLog c' - Real.negMulLog d') :
    a ^ (2 * a) * b ^ b * c ^ c * d ^ d ≤
      a' ^ (2 * a') * b' ^ b' * c' ^ c' * d' ^ d' := by
  rw [phi233_profile_product_as_entropy_exp a b c d ha hb hc hd,
    phi233_profile_product_as_entropy_exp a' b' c' d' ha' hb' hc' hd']
  exact Real.exp_le_exp.mpr hcost
