-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_original_weighted_drawdown_cdf_laplace
-- name    : AvramDividend.Classical.avram_ws01b_original_weighted_drawdown_cdf_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:28:16.093331+00:00
-- url     : https://prove2.me/theorems/830dccea-a3aa-48f4-b71a-b191824b862f
-- title:
--   Actual original exponential-clock weighted drawdown CDF has its precise spatial Laplace transform
-- statement:
--   For the actual original Lévy exponential-clock drawdown law ρ, its exponentially weighted law ζ has spatial cumulative ζ((−∞,x]) with precise positive-halfline Laplace transform 1/(β−φ) times the β-Laplace transform of ρ. This preserves any BV zero atom and is a genuine source stochastic input to the scalar killed q-scale capital transform, rather than a measure invented from desired scale identity.
-- source:
--   Accepted original real-clock drawdown measurability, actual supremum≥terminal and finite original exponential-clock product probability. Nonnegative Tonelli via accepted general positiveLaplace_cumulative_measure, retaining the BV atom at zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_original_weighted_drawdown_cdf_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r φ β : ℝ) (hr : 0 < r) (hφ : 0 < φ) (hβφ : φ < β) :
    let μ : Measure (Ω × ℝ) := P.prod (expMeasure r)
    let D : Ω × ℝ → ℝ :=
      fun z => runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1
    let ρ : Measure ℝ := Measure.map D μ
    let ζ : Measure ℝ := ρ.withDensity
      (fun z => ENNReal.ofReal (Real.exp (-φ * z)))
    (∫⁻ x : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-(β - φ) * x)) * ζ (Iic x)) =
      ENNReal.ofReal (1 / (β - φ)) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ρ) := by sorry
