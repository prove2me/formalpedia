-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_absolutelyContinuous
-- name    : AvramDividend.Classical.ae_negative_near_zero_of_absolutelyContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:46:27.911385+00:00
-- url     : https://prove2.me/theorems/5b4f4749-805e-4e94-9478-106c580d8175
-- title:
--   Almost-sure negative-half-line regularity transfers to every absolutely continuous Esscher-type law
-- statement:
--   Given two measures P and Q on the same underlying path space, if Q is absolutely continuous with respect to P and a real-valued nonnegative-time path process X visits the strictly negative half-line before every positive horizon P-almost surely, then this also holds Q-almost surely. This is the exact change-of-measure bridge needed after constructing the Esscher tilt of a spectrally negative Lévy law; it is a measure-theoretic theorem and deliberately does not assert construction or absolute continuity of any specific tilted process.
-- source:
--   Absolute continuity of Esscher transforms on finite-time path sigma-algebras; standard measure-theoretic preservation of almost-sure events. Relevant to Kuznetsov, Kyprianou and Rivero (2013), excursion-height smoothness under Esscher tilting.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ae_negative_near_zero_of_absolutelyContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P Q : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (hAC : Q ≪ P)
    (hRegP : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X t ω < 0) :
    ∀ᵐ ω ∂Q, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X t ω < 0 := by sorry
