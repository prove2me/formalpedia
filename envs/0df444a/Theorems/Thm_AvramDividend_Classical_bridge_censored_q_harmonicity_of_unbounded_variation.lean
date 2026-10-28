-- Prove2me | Theorems.Thm_AvramDividend_Classical_bridge_censored_q_harmonicity_of_unbounded_variation
-- name    : AvramDividend.Classical.bridge_censored_q_harmonicity_of_unbounded_variation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-26T07:34:30.036043+00:00
-- url     : https://prove2.me/theorems/889da773-b817-473f-a81b-95e52148e3fe
-- title:
--   Censored q-harmonicity of the scale function under unbounded variation without standing
-- statement:
--   Let X be spectrally negative Levy of unbounded variation, q>0, W its q-scale function, x real. For s<=u, on the event that shifted reserve x+X_s is nonnegative, the conditional expectation of the survival-indicated discounted scale payoff equals the indicated current scale value. This is the censored q-harmonicity premise needed by the killed-martingale interface without assuming Standing.
-- source:
--   IsScaleFunction first conjunct for negativity, SpectrallyNegativeLevy independent/stationary increments for strong-Markov killing; bridge for aed50a34 unbounded stopped-scale identity toward 09663d0d and 3e1ce2c8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.bridge_censored_q_harmonicity_of_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) :
    ∀ s u : ℝ≥0, s ≤ u →
      ({ω | 0 ≤ x + X.X s ω}).indicator
        (P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
          0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
         (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
           W (x + X.X u ω)) | 𝓕 s]) =ᵐ[P]
      ({ω | 0 ≤ x + X.X s ω}).indicator
        (fun ω => W (x + X.X s ω)) := by sorry
