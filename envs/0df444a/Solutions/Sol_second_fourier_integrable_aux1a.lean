-- Prove2me | solution 1 for second_fourier_integrable_aux1a
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:29:09.66813+00:00
-- url     : https://prove2.me/submissions/54e82b95-b04c-4c88-a9d6-6c82048a2b95

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set
open Complex hiding log

variable {x σ' : ℝ}

theorem solution (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simpa only [neg_mul, mul_neg, mul_comm] using
    (integrableOn_exp_mul_complex_Ioi (a := -((σ' : ℂ) - 1))
      (by simp; linarith) (-Real.log x))
