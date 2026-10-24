-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_levy_increment_tendsto_of_right_approximated_times
-- name    : AvramDividend.Classical.chat08_levy_increment_tendsto_of_right_approximated_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:25:52.368088+00:00
-- url     : https://prove2.me/theorems/b04caf6a-c94d-4e47-aff2-58341bd11128
-- title:
--   Right-approximating times preserve Lévy increments by pathwise right continuity
-- statement:
--   If nonnegative times T_n converge to t while all T_n≥t, then the increments X(T_n+u)−X(T_n) converge to X(t+u)−X(t) on every path. The Lévy structure directly supplies right continuity for each path; convergence of the shifted times and monotone domain constraints let us compose right-continuity and subtract the limits. This is a necessary pathwise limit component of approximating general stopping times by finite-valued stopping times in the missing strong Markov renewal proof.
-- source:
--   SpectrallyNegativeLevy.rightCont and Mathlib tendsto_nhdsWithin_iff, ContinuousWithinAt.tendsto, Tendsto.add, Tendsto.sub.

import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_levy_increment_tendsto_of_right_approximated_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (T : ℕ → ℝ≥0) (t u : ℝ≥0)
    (hT : Tendsto T atTop (𝓝 t)) (hbelow : ∀ n, t ≤ T n) :
    Tendsto (fun n => X.X (T n + u) ω - X.X (T n) ω)
      atTop (𝓝 (X.X (t + u) ω - X.X t ω)) := by sorry
