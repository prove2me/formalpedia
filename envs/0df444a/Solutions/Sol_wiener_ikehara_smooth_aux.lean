-- Prove2me | solution 1 for wiener_ikehara_smooth_aux
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:32:04.367451+00:00
-- url     : https://prove2.me/submissions/bf1d45e0-9cb2-4ed5-bb59-e6bf7488cd67

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SumIntegralComparisons

open Real MeasureTheory Set

variable {Ψ : ℝ → ℂ}

theorem solution (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by
  simpa [Complex.real_smul, Real.exp_neg, Real.exp_log hx, one_div] using
    (integral_comp_exp_Ioi Ψ (-Real.log x))
