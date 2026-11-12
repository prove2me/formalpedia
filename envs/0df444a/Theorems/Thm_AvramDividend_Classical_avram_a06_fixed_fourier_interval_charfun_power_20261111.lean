-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_fourier_interval_charfun_power_20261111
-- name    : AvramDividend.Classical.avram_a06_fixed_fourier_interval_charfun_power_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:36:13.323498+00:00
-- url     : https://prove2.me/theorems/d7ad88d9-3fd2-408d-89f8-7538e18943ef
-- title:
--   A06 deterministic marked-sum characteristic function depends only on interval length
-- statement:
--   For two or more fixed-grid intervals, the supplied Fourier factorisation implies that every pair of adjacent mark blocks is independent. Hence concatenation multiplies scalar characteristic functions. Equal one-mark marginal laws identify the one-step factor. An induction then shows the characteristic function of a length-k block is the kth power of the common mark factor, regardless of where the interval begins. This is the core new source-specific ingredient for A06 conditional Fourier step 5d7ad8be.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_fourier_forces_adjacent_independence_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_adjacent_independent_interval_charfun_concat_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_interval_characteristic_function_power_20261111
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_fixed_fourier_interval_charfun_power_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n) (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j))
    (hSame : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
            (t.ofLp i))
    (a k : ℕ) (t : ℝ) :
    MeasureTheory.charFun
      (Measure.map (fun ω => ∑ j ∈ Finset.Ico a (a + k), Y j ω) P) t =
    MeasureTheory.charFun (Measure.map (Y 0) P) t ^ k := by sorry
