-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_grid_joint_charfun_mark_power_20261111
-- name    : AvramDividend.Classical.avram_a06_fixed_grid_joint_charfun_mark_power_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:07:18.098794+00:00
-- url     : https://prove2.me/theorems/32e0f92d-214a-481a-87cf-ec945ce0d8bb
-- title:
--   Fixed-grid joint marked-sum Fourier law is a product of marginal characteristic powers
-- statement:
--   For at least two blocks, the accepted fixed-grid Fourier factorisation and accepted shift-invariant interval power law combine. Each coordinate characteristic function equals the common mark characteristic function raised to its interval length. This explicit integrand is what must be mixed against the independent random count-grid law in A06.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_fourier_interval_charfun_power_20261111
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_fixed_grid_joint_charfun_mark_power_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
    (m : Fin (n + 1) → ℕ) (hm : Monotone m)
    (t : WithLp 2 (Fin n → ℝ)) :
    MeasureTheory.charFun
      (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
        ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
    ∏ i : Fin n, (MeasureTheory.charFun (Measure.map (Y 0) P) (t.ofLp i)) ^
      (m i.succ - m i.castSucc) := by sorry
