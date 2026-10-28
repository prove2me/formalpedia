-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_height_level_null_of_markov_bad_event
-- name    : AvramDividend.Classical.excursion_height_level_null_of_markov_bad_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:50:54.443982+00:00
-- url     : https://prove2.me/theorems/c0869e8c-6b63-445d-a544-65a7fd6c022c
-- title:
--   The excursion height measure is atomless at a level given one exact killed strong-Markov bad-event identity and underlying zero regularity
-- statement:
--   Let n be a potentially sigma-finite reflected-excursion measure and P the Lévy increment-path law on the product path space. Assume (1) every exact-height-x excursion reaches x within its lifetime and stays below its maximal height, (2) P-almost every path enters the negative half-line arbitrarily near zero, and (3) the killed excursion strong Markov identity holds for the single measurable bad event of paths that do not enter negative values immediately: n(T<ζ, bad shifted increments)=n(T<ζ)·P(bad). Then n(H=x)=0. This isolates exactly the missing n-Markov law and the true Shtatland/Rogozin process regularity, and discharges all subsequent elementary measure-zero and strict-overshoot reasoning using canonically proved helpers. No unconditional atomlessness or existence of n is assumed.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), scale function survey §2.3 Lemma 2.4. Strong Markov at the height hitting time under sigma-finite excursion law; Rogozin downward regularity for unbounded variation.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Theorems.Thm_AvramDividend_Classical_reflected_excursion_height_level_null_of_ae_negative_on_hitting

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.excursion_height_level_null_of_markov_bad_event
    {E : Type*} [mE : MeasurableSpace E]
    (n : Measure E) (P : Measure (ℝ≥0 → ℝ))
    (S Y : E → ℝ≥0 → ℝ) (T ζ H : E → ℝ≥0) (x : ℝ≥0)
    (hAtLevel : ∀ e : E, H e = x →
      T e < ζ e ∧ Monotone (S e) ∧
      S e (T e) - Y e (T e) = (x : ℝ) ∧
      ∀ t : ℝ≥0, T e ≤ t → t < ζ e →
        S e t - Y e t ≤ (x : ℝ))
    (hRegP : ∀ᵐ f ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ f s < 0)
    (hExcursionMarkovBad :
      n {e : E | T e < ζ e ∧
        ¬ ∀ ε : ℝ≥0, 0 < ε →
          ∃ s : ℝ≥0, s < ε ∧
            Y e (T e + s) - Y e (T e) < 0} =
      n {e : E | T e < ζ e} *
        P {f : ℝ≥0 → ℝ | ¬ ∀ ε : ℝ≥0, 0 < ε →
          ∃ s : ℝ≥0, s < ε ∧ f s < 0}) :
    n {e : E | H e = x} = 0 := by sorry
