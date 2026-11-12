-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_conditional_fourier_two_or_more_20261111
-- name    : AvramDividend.Classical.avram_a06_conditional_fourier_two_or_more_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:14:54.344987+00:00
-- url     : https://prove2.me/theorems/64473210-1a0c-4e7e-8c12-c8dfe057adf3
-- title:
--   A06 nontrivial random-count-grid Fourier mixing with two or more intervals
-- statement:
--   This isolates the substantive n≥2 step of the conditional Fourier representation for independent count and mark streams. n=0 is already proved and n=1 has a published constant-factor helper and a pending dedicated closure. For n≥2, use the proved deterministic-grid Fourier power formula, measurable marked sums, and independent-pair pushforward product law to integrate over the random count grid.

import Mathlib
open MeasureTheory Set ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_conditional_fourier_two_or_more_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n)
    (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hNmono : ∀ ω, Monotone (fun i => N i ω))
    (hSameLaw : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P)
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
              (t.ofLp i)) :
    ∀ t : WithLp 2 (Fin n → ℝ), ∃ φ : Fin n → ℕ → ℂ,
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
          ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) P) t =
          ∫ ω, ∏ i : Fin n, φ i (N i.succ ω - N i.castSucc ω) ∂P
      ∧ ∀ i : Fin n, MeasureTheory.charFun
          (Measure.map (fun ω : Ω =>
            ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P)
          (t.ofLp i) =
          ∫ ω, φ i (N i.succ ω - N i.castSucc ω) ∂P := by sorry
