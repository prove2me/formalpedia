-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_fourier_forces_adjacent_independence_20261111
-- name    : AvramDividend.Classical.avram_a06_fixed_fourier_forces_adjacent_independence_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:31:45.802056+00:00
-- url     : https://prove2.me/theorems/0168d628-1002-4384-9b7f-5317164167ac
-- title:
--   The A06 finite-grid Fourier hypothesis forces independence of any two consecutive intervals
-- statement:
--   For n at least two, embed any three monotone endpoints a≤b≤c as the first three points of an n+1 grid, filling the remaining positions with c. The fixed-grid Fourier identity gives mutual independence by the proved converse characteristic-function lemma; its first two interval sums are therefore independent.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_fourier_factor_implies_block_independence_20261111
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_fixed_fourier_forces_adjacent_independence_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n) (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j))
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
            (t.ofLp i))
    (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    IndepFun (fun ω => ∑ j ∈ Finset.Ico a b, Y j ω)
      (fun ω => ∑ j ∈ Finset.Ico b c, Y j ω) P := by sorry
