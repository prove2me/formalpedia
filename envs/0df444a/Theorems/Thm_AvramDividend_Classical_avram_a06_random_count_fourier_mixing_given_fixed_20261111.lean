-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_random_count_fourier_mixing_given_fixed_20261111
-- name    : AvramDividend.Classical.avram_a06_random_count_fourier_mixing_given_fixed_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:51:42.163776+00:00
-- url     : https://prove2.me/theorems/efc6c2ea-fe12-4d0f-b2f6-6a89755a7f65
-- title:
--   Mix the fixed-grid Fourier factorisation over independent random count increments
-- statement:
--   This separates the random-count mixing argument from deterministic mark-block independence. Assume that every deterministic ordered count-grid has factorised vector characteristic functions, and that the count increments are independent, identically distributed marks have a common law, and the entire count grid is independent of the mark sequence. Prove that the random-grid block sums also have factorised characteristic functions. The fixed-grid hypothesis is already supplied by theorem 0190fb85, thus this is the remaining substantive A06 Fourier-mixing obligation under 23364f73.

import Mathlib
open MeasureTheory Set ProbabilityTheory Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_random_count_fourier_mixing_given_fixed_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hNmono : ∀ ω, Monotone (fun i => N i ω))
    (hCount : iIndepFun (fun (i : Fin n) ω =>
      N i.succ ω - N i.castSucc ω) P)
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
        ∏ i : Fin n, MeasureTheory.charFun
          (Measure.map (fun ω : Ω =>
            ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P)
          (t.ofLp i) := by sorry
