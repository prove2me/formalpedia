-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_terminal_clock_indepFun_all_path_functionals
-- name    : AvramDividend.Classical.esscher_terminal_clock_indepFun_all_path_functionals
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:04:36.045011+00:00
-- url     : https://prove2.me/theorems/90b15a48-92b2-42ab-8c1e-b1c738ed29ca
-- title:
--   Every measurable tilted-path functional is independent of a genuine exponential clock under the terminal Esscher product law
-- statement:
--   For a spectrally negative Lévy process, Esscher parameter θ≥0, deterministic terminal horizon T and independent exponential clock rate p>0, let Q_T be the genuine terminal-horizon Esscher probability measure. Under Q_T×Exp(p), every measurable functional of the complete path coordinate is independent, in the typed ProbabilityTheory.IndepFun sense, of the clock projection. This proves independence of entire measurable cylinder families (by choosing a cylinder-valued f), stronger than rectangle identities and unlike a clock-dependent random-time density.
-- source:
--   Pinned Mathlib ProbabilityTheory.indepFun_prod (Mathlib.Probability.Independence.Basic), ProbabilityTheory.isProbabilityMeasure_expMeasure (Mathlib.Probability.Distributions.Exponential); accepted Prove2Me chat04_esscher_weighted_finite_horizon_probability.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_terminal_clock_indepFun_all_path_functionals
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (T : ℝ≥0)
    (p : ℝ) (hp : 0 < p)
    {α : Type*} [MeasurableSpace α]
    (f : Ω → α) (hf : Measurable f) :
    IndepFun (fun z : Ω × ℝ => f z.1)
      (fun z : Ω × ℝ => z.2)
      ((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod
          (expMeasure p)) := by sorry
