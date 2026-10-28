-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_charFun
-- name    : AvramDividend.Classical.cross_levy_whole_path_law_of_equal_charFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:36:58.601917+00:00
-- url     : https://prove2.me/theorems/23820eb7-356e-472a-81f3-449f65415c15
-- title:
--   Matching all one-time characteristic functions identifies the complete laws of distinct Lévy path processes
-- statement:
--   Two spectrally negative Lévy processes on unrelated probability spaces whose one-time characteristic functions agree for every time and real Fourier argument induce identical probability measures on the complete real-valued coordinate path space. Apply the accepted Fourier uniqueness theorem at each time, followed by the new cross-space whole-path law theorem from all marginal distributions. In particular, this can transfer path-count event probabilities from a canonical Lévy realization to an arbitrary realization once their characteristic exponents are matched.
-- source:
--   Composition of Proved AvramDividend.Classical.cross_levy_marginal_laws_of_equal_charFun [7888da5c-93f5-4178-9acc-b21d685e7836] and published AvramDividend.Classical.cross_levy_whole_path_law_of_equal_marginals [99d73ada-1f35-4196-aa9d-fd7b1e29012b]. Publish only after the second theorem has a Proved verdict.

import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_marginals
import Theorems.Thm_AvramDividend_Classical_cross_levy_marginal_laws_of_equal_charFun

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_whole_path_law_of_equal_charFun
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hchar : ∀ t : ℝ≥0, ∀ ξ : ℝ,
      charFun (Measure.map (X.X t) P₁) ξ =
      charFun (Measure.map (Y.X t) P₂) ξ) :
    Measure.map (fun ω : Ω₁ => fun u : ℝ≥0 => X.X u ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun u : ℝ≥0 => Y.X u ω) P₂ := by sorry
