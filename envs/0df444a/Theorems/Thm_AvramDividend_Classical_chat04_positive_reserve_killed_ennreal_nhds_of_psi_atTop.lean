-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_ennreal_nhds_of_psi_atTop
-- name    : AvramDividend.Classical.chat04_positive_reserve_killed_ennreal_nhds_of_psi_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:36:46.993866+00:00
-- url     : https://prove2.me/theorems/5a4a8557-5341-4a7c-87cb-35a6688533c8
-- title:
--   Time-zero killed q-scale continuity from diverging Lévy exponent
-- statement:
--   If the Levy Laplace exponent tends to positive infinity, every nonnegative discount admits a nonnegative exponential parameter above it. The previously Proved history-killed ENNReal time-zero continuity then applies without choosing a rate parameter in the theorem statement. This removes the extraneous growth-witness argument en route to the all-time killed q-scale identity.
-- source:
--   Direct composition of Proved eventual_psi_above_q_of_tendsto_atTop and chat04_positive_reserve_killed_ennreal_expectation_nhds_no_schedule. Future import by positive-reserve killed q-scale semigroup and the open all-time stopped-scale identity a885f0b3.

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_ennreal_expectation_nhds_no_schedule
import Theorems.Thm_AvramDividend_Classical_eventual_psi_above_q_of_tendsto_atTop

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_positive_reserve_killed_ennreal_nhds_of_psi_atTop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x)
    (hψdiv : Tendsto X.ψ atTop atTop) :
    Tendsto
      (fun t : ℝ≥0 => ∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)
      (𝓝 0) (𝓝 (ENNReal.ofReal (W x))) := by sorry
