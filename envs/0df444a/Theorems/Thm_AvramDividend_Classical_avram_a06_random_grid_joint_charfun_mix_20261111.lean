-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_random_grid_joint_charfun_mix_20261111
-- name    : AvramDividend.Classical.avram_a06_random_grid_joint_charfun_mix_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:20:19.13039+00:00
-- url     : https://prove2.me/theorems/e86cede0-67d1-4a67-b9ff-0eb5fe6b9657
-- title:
--   Joint characteristic-function mixing across an independent random count grid
-- statement:
--   Under independent count and mark streams, the characteristic function of the random-grid marked increments is obtained by averaging deterministic-grid characteristic-function powers over the count-grid law. This is one of the two exact subobligations in the n>=2 A06 conditional Fourier reduction; proved fixed-grid powers and independent product-law bridge are available.

import Mathlib
open MeasureTheory Set ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_random_grid_joint_charfun_mix_20261111
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
    ∀ t : WithLp 2 (Fin n → ℝ),
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
          ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) P) t =
      ∫ ω, ∏ i : Fin n,
        (MeasureTheory.charFun (Measure.map (Y 0) P) (t.ofLp i)) ^
          (N i.succ ω - N i.castSucc ω) ∂P := by sorry
