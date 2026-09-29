-- Prove2me | solution 1 for euler_partial_product_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T06:36:08.211174+00:00
-- url     : https://prove2.me/submissions/84801140-694c-47a4-9ae8-89ae8410c5a2

import Mathlib
import Definitions.Def_timepiece_corrector
open Complex Finset Filter Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ z ∈ Metric.ball c r, z.re > 1 / 2)
    (P : ℕ) (ω : Ω_infty) (K : ℕ) :
    let g : ℂ → ℂ := fun s => ∏ p ∈ (Finset.Icc 2 K).filter Nat.Prime,
      (1 - X_p p P ω / (p : ℂ) ^ s)
    AnalyticOnNhd ℂ g (Metric.ball c r) ∧
    ∀ z ∈ Metric.ball c r, g z ≠ 0 := by
      refine' ⟨ _, fun z hz => _ ⟩;
      · apply_rules [ DifferentiableOn.analyticOnNhd ];
        · refine' DifferentiableOn.congr _ _;
          exact fun s => ∏ p ∈ Finset.filter Nat.Prime ( Finset.Icc 2 K ), ( 1 - X_p p P ω * Complex.exp ( -s * Complex.log p ) );
          · fun_prop;
          · intro z hz; refine' Finset.prod_congr rfl fun p hp => _; rw [ Complex.cpow_def_of_ne_zero ( Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2 ) ] ; ring;
            rw [ ← Complex.exp_neg ];
        · exact Metric.isOpen_ball;
      · -- For each prime $p$, $|X_p / p^z| = |X_p| \cdot |p^{-z}| = 1 \cdot p^{-\text{Re}(z)} \leq 2^{-\text{Re}(z)} < 1$ since $\text{Re}(z) > 1/2$.
        have h_abs : ∀ p : ℕ, Nat.Prime p → p ∈ Finset.Icc 2 K → ‖X_p p P ω / (p : ℂ) ^ z‖ < 1 := by
          intro p hp hpK
          have h_abs : ‖X_p p P ω‖ = 1 := by
            unfold X_p; split_ifs <;> norm_num [ Complex.norm_exp ] ;
          have h_abs_p : ‖(p : ℂ) ^ z‖ = (p : ℝ) ^ z.re := by
            rw [ ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos ( Nat.cast_pos.mpr hp.pos ) ]
          simp [h_abs, h_abs_p];
          exact inv_lt_one_of_one_lt₀ ( Real.one_lt_rpow ( mod_cast hp.one_lt ) ( by linarith [ hball z hz ] ) );
        exact Finset.prod_ne_zero_iff.mpr fun p hp => sub_ne_zero_of_ne <| Ne.symm <| by intro h; have := h_abs p ( Finset.mem_filter.mp hp |>.2 ) ( Finset.mem_filter.mp hp |>.1 ) ; norm_num [ h ] at this;
