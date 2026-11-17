-- Prove2me | solution 1 for thm_5_11
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:14:04.53906+00:00
-- url     : https://prove2.me/submissions/aad52fae-f12a-4fe5-8707-6d1a833b09a4

import Definitions.Def_ProbabilityTheory_chapter_05_thm_5_11_F000
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter

theorem solution {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (X : ℕ → Ω → β) (h_meas : ∀ n, Measurable (X n))
    (h_indep : ProbabilityTheory.iIndepFun X P) {t : Set Ω}
    (ht_tail : @MeasurableSet Ω (tailSigmaAlgebra X) t) :
    P t = 0 ∨ P t = 1 := by
  let s : ℕ → MeasurableSpace Ω := fun n => MeasurableSpace.comap (X n) ‹MeasurableSpace β›
  have h_le : ∀ n, s n ≤ ‹MeasurableSpace Ω› := fun n => (h_meas n).comap_le
  simpa [s, tailSigmaAlgebra] using
    ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop
      (μ := P) h_le h_indep.iIndep ht_tail
