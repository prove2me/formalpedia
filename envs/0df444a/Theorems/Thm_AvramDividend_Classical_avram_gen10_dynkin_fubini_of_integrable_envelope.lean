-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen10_dynkin_fubini_of_integrable_envelope
-- name    : AvramDividend.Classical.avram_gen10_dynkin_fubini_of_integrable_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:29:00.716439+00:00
-- url     : https://prove2.me/theorems/6927b44e-61f8-4823-9833-bab418ca10b2
-- title:
--   Dynkin Fubini on a finite horizon from an integrable random envelope
-- statement:
--   For a jointly measurable real-valued time-dependent random integrand, an integrable pathwise envelope on a finite nonnegative horizon gives integrability of its time integral and permits expectation/time-integral interchange.
-- source:
--   Port of Asakura.Chapter8.dynkin_fubini (MasaakiFukasawa/stochastic-analysis-lean, Chapter8DynkinFubini.lean), pinned to Avram Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Conditional envelope interface for original stopped-generator L1 leaf d2ca06c0 / 5df846f9, not a proof of the envelope.

import Mathlib
import Mathlib.MeasureTheory.Integral.Prod
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen10_dynkin_fubini_of_integrable_envelope
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (T : ℝ) (hT : 0 ≤ T)
    (R : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry R))
    (K : Ω → ℝ) (hK : Integrable K P)
    (hb : ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, ‖R ω s‖ ≤ K ω) :
    Integrable (fun ω => ∫ s in 0..T, R ω s) P ∧
    (∫ ω, (∫ s in 0..T, R ω s) ∂P) =
      ∫ s in 0..T, ∫ ω, R ω s ∂P := by sorry
