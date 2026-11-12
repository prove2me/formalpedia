-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_fourier_factor_implies_block_independence_20261111
-- name    : AvramDividend.Classical.avram_a06_fixed_fourier_factor_implies_block_independence_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:26:45.817974+00:00
-- url     : https://prove2.me/theorems/95b402cd-ed6a-4245-95b9-1c620d1d9f0d
-- title:
--   Fixed-grid Fourier product identity implies independence of all marked interval sums
-- statement:
--   The characteristic-function factorisation hypothesis used in the A06 conditional Fourier problem is exactly Mathlib's characterisation of finite-family independence. Consequently the deterministic blocks of every monotone count grid are independent. This allows the A06 Fourier power and disintegration lemmas to be instantiated without separately assuming independence.

import Mathlib
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_fixed_fourier_factor_implies_block_independence_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ) (Y : ℕ → Ω → ℝ) (hY : ∀ j, Measurable (Y j))
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
            (t.ofLp i))
    (m : Fin (n + 1) → ℕ) (hm : Monotone m) :
    iIndepFun (fun i : Fin n => fun ω : Ω =>
      ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P := by sorry
