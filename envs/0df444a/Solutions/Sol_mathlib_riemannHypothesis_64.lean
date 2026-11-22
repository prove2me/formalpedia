-- Prove2me | solution 64 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:28.257648+00:00
-- url     : https://prove2.me/submissions/884ce737-fed3-41eb-93e0-d0696f704735
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_compensated_resolvent_defect_series
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_compensated_resolvent_kernel_pos
import Theorems.Thm_MasulloRH_single_resolvent_test
import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_MasulloRH_omitted_zero_cancellation_iff_RH

-- Step 1: `MasulloRH.compensated_resolvent_defect_series` implies `MasulloRH.compensated_resolvent_trace_tail_bound` (accepted reduction of `MasulloRH.compensated_resolvent_trace_tail_bound`).
section

open MasulloRH

theorem MasulloRH.compensated_resolvent_trace_tail_bound
    (α : ℝ) (hα : 0 < α) (hsmall : α < 1 / 2)
    (hkernel :
      ∀ (β γ T : ℝ), 0 ≤ β → β ≤ 1 → 36 ≤ γ ^ 2 →
        let a := 3 - β
        let b := 5 / 2 - β
        let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
        let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
        0 < k ∧ a / (a ^ 2 + (T - γ) ^ 2) ≤ k) :
    0 ≤ (regularizedTraceRHS α 3).re - (regularizedTraceRHS (1 / 2) 3).re := by
  rcases compensated_resolvent_defect_series α hα hsmall hkernel with ⟨f, hf, _hs, hEq⟩
  rw [hEq]
  have hsum : 0 ≤ ∑' ρ : ZetaZerosInTraceStrip (1 / 2), f ρ :=
    tsum_nonneg hf
  exact hsum

end

-- Step 2: `MasulloRH.compensated_resolvent_trace_tail_bound` implies `MasulloRH.regularized_trace_scalar_lower_bound` (accepted reduction of `MasulloRH.regularized_trace_scalar_lower_bound`).
section

open MasulloRH

theorem MasulloRH.regularized_trace_scalar_lower_bound (α : ℝ) (hα : 0 < α) (hsmall : α < 1 / 2) :
    (zetaLogDeriv 3).re ≤ (regularizedTraceRHS α 3).re := by
  have hkernel :
      ∀ (β γ T : ℝ), 0 ≤ β → β ≤ 1 → 36 ≤ γ ^ 2 →
        let a := 3 - β
        let b := 5 / 2 - β
        let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
        let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
        0 < k ∧ a / (a ^ 2 + (T - γ) ^ 2) ≤ k := by
    intro β γ T hβ0 hβ1 hγ
    exact compensated_resolvent_kernel_pos β γ T hβ0 hβ1 hγ
  have htail := compensated_resolvent_trace_tail_bound α hα hsmall hkernel
  have hfull := regularized_initial_identity_full_strip (3 : ℂ) (by norm_num)
  have hre : (regularizedTraceRHS (1 / 2) 3).re = (zetaLogDeriv 3).re :=
    congrArg Complex.re hfull
  nlinarith

end

-- Step 3: `MasulloRH.regularized_trace_scalar_lower_bound` implies `MasulloRH.narrow_window_omitted_zero_sum` (accepted reduction of `MasulloRH.narrow_window_omitted_zero_sum`).
section

open MasulloRH

theorem MasulloRH.narrow_window_omitted_zero_sum (α : ℝ) (hα : 0 < α) (hsmall : α < 1/2)
    (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
    (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0 := by
  have hbound := regularized_trace_scalar_lower_bound α hα hsmall
  rw [← regularized_initial_identity_full_strip 3 (by norm_num)] at hbound
  have hin := (single_resolvent_test α).mp hbound
  let O := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
  have : IsEmpty O := by
    constructor
    intro r
    obtain ⟨hz, h0, h1⟩ := r.val.property
    have hfull : |r.val.val.re - 1/2| < 1/2 := by
      rw [abs_lt]
      constructor <;> linarith
    exact (not_lt_of_ge r.property) (hin ⟨r.val.val, hz, h0, h1, hfull⟩)
  change (∑' r : O, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0
  simp

end

-- Step 4: `MasulloRH.narrow_window_omitted_zero_sum` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis :=
  MasulloRH.omitted_zero_cancellation_iff_RH.mp
    (fun α hα hsmall φ hφ =>
      MasulloRH.narrow_window_omitted_zero_sum α hα hsmall φ hφ)

end
