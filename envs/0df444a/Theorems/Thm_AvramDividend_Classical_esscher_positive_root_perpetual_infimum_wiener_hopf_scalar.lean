-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_perpetual_infimum_wiener_hopf_scalar
-- name    : AvramDividend.Classical.esscher_positive_root_perpetual_infimum_wiener_hopf_scalar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:34:03.866599+00:00
-- url     : https://prove2.me/theorems/07c7d8b4-44ae-416c-8ef4-c205398f5876
-- title:
--   Wiener–Hopf scalar Laplace transform for the true perpetual Esscher infimum law
-- statement:
--   For a spectrally negative Lévy process and q>0 with a positive Esscher root φ satisfying ψ(φ)=q, there are a probability distribution ν of the actual Esscher perpetual reflected running infimum and a strictly positive scalar m such that the Laplace transform of ν at every β>0 is mβ/(ψ(φ+β)−q). The CDF of ν is exactly the infimum over finite Esscher-horizon survival expectations, as in the published canonical full-mass theorem. The scalar m is necessarily the tilted mean ψ′(φ) when that derivative is formalised. This is the crucial genuine stochastic Wiener–Hopf factorisation, not a consequence of the distribution’s total mass alone.
-- source:
--   A. Kuznetsov, A. E. Kyprianou and V. Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, spatial Wiener–Hopf factorisation and descending ladder potential. DOI/published: https://people.bath.ac.uk/ak257/scale-review-final.pdf. Required by Avram, Palmowski, Pistorius (2007), optimal dividend problem and Esscher scale asymptotics.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_perpetual_infimum_probability_full_mass
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_perpetual_survival_cumulative_laplace_is_measure_laplace
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_positive_root_perpetual_infimum_wiener_hopf_scalar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (ν : Measure ℝ) (m : ℝ),
      IsProbabilityMeasure ν ∧ 0 < m ∧
      (∀ x : ℝ, ν (Iic x) =
        (⨅ t : ℝ≥0, ENNReal.ofReal
          (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
            (fun ω => Real.exp (φ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ω ∂P))) ∧
      (∀ β : ℝ, 0 < β →
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν) =
          ENNReal.ofReal (m * β / (X.ψ (φ + β) - q))) := by sorry
