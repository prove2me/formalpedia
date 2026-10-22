-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_scaledW_endpoint_harmonic_of_continuous_residual
-- name    : AvramDividend.Classical.chat07_scaledW_endpoint_harmonic_of_continuous_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:35:10.564659+00:00
-- url     : https://prove2.me/theorems/ecc1d16c-dca5-49a3-945f-8eff6d07138f
-- title:
--   Exact normalised scale-function generator harmonicity at a positive barrier from interior continuity
-- statement:
--   If a positive barrier endpoint a admits a scale function W in the Lévy generator domain, whose generator residual ΓW−qW is continuous on (0,a] and vanishes on (0,a), then the normalised scale-function branch z↦divE(W z,scaleDeriv W a) is generator-integrable and exactly q-harmonic at a. First transfer the residual to a by continuity and then apply the proved generator scalar-transport theorem. The conclusion is a rigorous cap-matching bridge under explicit analytic assumptions; it does not derive the stochastic harmonicity hypotheses from the scale-function transform.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_scaledW_endpoint_harmonic_of_continuous_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (a : ℝ) (ha : 0 < a)
    (hdom : X.GeneratorIntegrable W a)
    (hcont : ContinuousOn
      (fun z : ℝ => X.generator W z - q * W z) (Ioc 0 a))
    (hinside : ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0) :
    X.GeneratorIntegrable
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) a ∧
      X.generator
        (fun z : ℝ => divE (W z) (scaleDeriv W a)) a -
        q * divE (W a) (scaleDeriv W a) = 0 := by sorry
