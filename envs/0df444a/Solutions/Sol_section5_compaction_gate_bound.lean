-- Prove2me | solution 1 for section5_compaction_gate_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:15.091963+00:00
-- url     : https://prove2.me/submissions/982a90a8-5fb2-4461-aacc-67115a977401

import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_gates12
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Explicit swap circuits for the outcome-dependent compaction in Theorem 5.4. -/































theorem section5_particle_register_width (n : ℕ) (hn : 1 ≤ n) :
    ((Nat.clog 2 n+1 : ℕ) : ℝ) ≤ (3/Real.log 2)*Real.log (n+1) := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hn')
  have hceil : ⌈Real.logb (2:ℝ) (n:ℝ)⌉₊ = Nat.clog 2 n := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 n
  rw [hceil] at hc
  have hc' := mul_le_mul_of_nonneg_right hc.le hp.le
  rw [Real.logb,add_mul,div_mul_cancel₀ _ hp.ne',one_mul] at hc'
  have hlog : Real.log (n:ℝ) ≤ Real.log (n+1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log (n+1) :=
    Real.log_le_log (by norm_num) (by linarith)
  rw [Nat.cast_add,Nat.cast_one,div_mul_eq_mul_div]
  apply (le_div_iff₀ hp).mpr
  nlinarith



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem solution (n K : ℕ) (hn : 1 ≤ n) :
    ((2*K*(Nat.clog 2 n+1) : ℕ) : ℝ) ≤ (6/Real.log 2)*K*Real.log (n+1) := by
  calc
    _ = (2*(K:ℝ))*((Nat.clog 2 n+1 : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (2*(K:ℝ))*((3/Real.log 2)*Real.log (n+1)) :=
      mul_le_mul_of_nonneg_left (section5_particle_register_width n hn) (by positivity)
    _ = _ := by ring
