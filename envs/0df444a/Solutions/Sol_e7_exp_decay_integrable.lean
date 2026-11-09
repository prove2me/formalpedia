-- Prove2me | solution 1 for e7_exp_decay_integrable
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T06:54:44.330208+00:00
-- url     : https://prove2.me/submissions/a2a06520-c004-4d94-88c8-3eee5719a358

import Mathlib

open MeasureTheory

theorem solution (rate : ℝ) (hrate : 0 < rate) :
    IntegrableOn (fun t : ℝ => Real.exp (-rate * t)) (Set.Ioi 0) volume :=
  exp_neg_integrableOn_Ioi 0 hrate
