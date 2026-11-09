-- Prove2me | solution 1 for e7_integral_split_weighted_residual
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:44:27.372478+00:00
-- url     : https://prove2.me/submissions/9910ce09-792f-4b54-9580-77bd6bc10eaf

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a b c W : Ω → ℝ)
    (ha : Integrable (fun ω => a ω * W ω) P)
    (hb : Integrable (fun ω => b ω * W ω) P)
    (hc : Integrable (fun ω => c ω * W ω) P)
    (hres : (∫ ω, (a ω - b ω - c ω) * W ω ∂P) = 0) :
    (∫ ω, a ω * W ω ∂P) - (∫ ω, b ω * W ω ∂P) =
      ∫ ω, c ω * W ω ∂P := by
  have h : (∫ ω, (a ω - b ω - c ω) * W ω ∂P) =
      (∫ ω, a ω * W ω ∂P) - (∫ ω, b ω * W ω ∂P) - ∫ ω, c ω * W ω ∂P := by
    have hab : Integrable (fun ω => a ω * W ω - b ω * W ω) P := ha.sub hb
    rw [show (fun ω => (a ω - b ω - c ω) * W ω) =
      (fun ω => (a ω * W ω - b ω * W ω) - c ω * W ω) by
        funext ω; ring]
    rw [integral_sub hab hc, integral_sub ha hb]
  linarith
