-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_negative_exp_integrable
-- name    : AvramDividend.Classical.chat04_esscher_finite_negative_exp_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:44:57.672392+00:00
-- url     : https://prove2.me/theorems/5f024df2-c837-4a6f-b024-186ad8a40211
-- title:
--   The negative endpoint exponential is integrable under each genuine finite-time Esscher law
-- statement:
--   For a spectrally negative Lévy process and finite Esscher tilt θ≥0, the random variable exp(−εX_t) is integrable under the actual finite-horizon density-weighted probability law for every ε∈[0,θ]. This upgrades the existing real integral identity to a genuine finite exponential moment suitable for nonnegative Markov and path-tail estimates.
-- source:
--   Apply pinned `MeasureTheory.integrable_withDensity_iff` for a measurable everywhere finite Esscher density; transform exp(−εX_t)×density into exp(−tψθ)×exp((θ−ε)X_t); the latter is integrable by the defining Lévy exponential moment at θ−ε≥0. This is independent of Wiener–Hopf.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Process.Adapted
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_finite_negative_exp_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ ε : ℝ) (hθ : 0 ≤ θ)
    (hε : 0 ≤ ε) (hεθ : ε ≤ θ) :
    Integrable (fun ω => Real.exp (-ε * X.X t ω))
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal
          (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)))) := by sorry
