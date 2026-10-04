-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_rearrangement_of_integrable
-- name    : AvramDividend.Classical.bv_laplace_exponent_rearrangement_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T08:10:52.796666+00:00
-- url     : https://prove2.me/theorems/ddf1b11b-8bcd-4324-8cfd-2e0b02d99982
-- title:
--   Exact bounded-variation Lévy–Khintchine drift and jump-integral rearrangement
-- statement:
--   For the actual Classical spectrally negative Lévy process, once the two explicit real-valued integrability hypotheses are established, bounded variation implies that the Gaussian term vanishes and the compensation indicator on (-1,1) cancels exactly against the drift adjustment on (-1,0). The canonical Laplace exponent therefore equals δθ plus the uncompensated negative-jump exponential integral. This is the central algebraic reduction needed before the jump-magnitude map and positive renewal kernel transform are applied.
-- source:
--   Canonical Classical SpectrallyNegativeLevy definition 933ced80-71c1-4c0f-a6a7-ab7757fc97e9, pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_laplace_exponent_rearrangement_of_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation) (θ : ℝ)
    (hexp : IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) X.ν)
    (hcomp : IntegrableOn
      (fun y : ℝ => θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (Iio (0 : ℝ)) X.ν) :
    X.ψ θ = X.drift * θ +
      ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂X.ν := by
  sorry
