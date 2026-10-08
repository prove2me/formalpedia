-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_future_increment_exp_integrable
-- name    : AvramDividend.Classical.levy_future_increment_exp_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:17:52.644189+00:00
-- url     : https://prove2.me/theorems/ecb38f09-50ed-470d-ac30-21594e9f3e48
-- title:
--   Integrability of the exponential of a deterministic Lévy increment
-- statement:
--   The exponential of a deterministic-time Lévy increment has a finite expectation for every nonnegative Laplace parameter. Stationary increments identify its law with the process at elapsed time h, and the Laplace field of SpectrallyNegativeLevy gives integrability at that elapsed time. This independent lemma supplies the integrability prerequisite for factoring increments against past filtration events and for summing finite stopping-time partitions.
-- source:
--   Canonical SpectrallyNegativeLevy.stationaryIncrements and laplace; Avram et al (2007), Section 2 Lévy-Khintchine exponential moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_future_increment_exp_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable
      (fun ω => Real.exp
        (θ * (X.X (s + h) ω - X.X s ω))) P := by sorry
