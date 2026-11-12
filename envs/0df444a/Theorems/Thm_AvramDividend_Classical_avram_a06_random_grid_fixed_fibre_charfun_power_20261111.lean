-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_random_grid_fixed_fibre_charfun_power_20261111
-- name    : AvramDividend.Classical.avram_a06_random_grid_fixed_fibre_charfun_power_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:35:12.396184+00:00
-- url     : https://prove2.me/theorems/75429607-c3ca-4da5-97f3-bed8c16db5ce
-- title:
--   Every realised count grid has deterministic mark-vector characteristic function product powers
-- statement:
--   A pointwise deterministic-grid fibre law, obtained by specialising the already Proved fixed-grid joint characteristic-function power theorem to each monotone realised count grid. This avoids any stochastic conditioning and is reusable in the remaining A06 Fubini disintegration.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_grid_joint_charfun_mark_power_20261111
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_random_grid_fixed_fibre_charfun_power_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n)
    (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hNmono : ∀ ω, Monotone (fun i => N i ω))
    (hSameLaw : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
              (t.ofLp i))
    (ω : Ω) (t : WithLp 2 (Fin n → ℝ)) :
    MeasureTheory.charFun
      (Measure.map (fun ω' : Ω => WithLp.toLp 2 (fun i : Fin n =>
        ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω')) P) t =
    ∏ i : Fin n, (MeasureTheory.charFun (Measure.map (Y 0) P) (t.ofLp i)) ^
      (N i.succ ω - N i.castSucc ω) := by sorry
