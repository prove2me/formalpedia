-- Prove2me | solution 37 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:50.356627+00:00
-- url     : https://prove2.me/submissions/ea6af403-51ef-4316-954a-1f9a5f581cac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_regularized_trace_scalar_lower_bound
import Theorems.Thm_MasulloRH_single_resolvent_test
import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_MasulloRH_omitted_zero_cancellation_iff_RH

-- Step 1: `MasulloRH.regularized_trace_scalar_lower_bound` implies `MasulloRH.narrow_window_omitted_zero_sum` (accepted reduction of `MasulloRH.narrow_window_omitted_zero_sum`).
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

-- Step 2: `MasulloRH.narrow_window_omitted_zero_sum` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis :=
  MasulloRH.omitted_zero_cancellation_iff_RH.mp
    (fun α hα hsmall φ hφ =>
      MasulloRH.narrow_window_omitted_zero_sum α hα hsmall φ hφ)

end
