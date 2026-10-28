-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_native_variance_coefficient
-- name    : AvramDividend.Classical.gaussian_esscher_volterra_native_variance_coefficient
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:47:33.249613+00:00
-- url     : https://prove2.me/theorems/9bffb490-a36d-4916-9340-d3e193fdfd25
-- title:
--   Exact Gaussian variance coefficient in the canonical Esscher Volterra equation
-- statement:
--   The Gaussian Esscher integrated scale equation has the exact leading coefficient sigma squared divided by two. Extract the native drift and Gaussian jump double-tail kernel from the existing canonical Volterra identity and its proven L1 integrability. This replaces the non-identifying existential coefficient in other proved Gaussian Volterra theorems and is needed to derive the right slope 2/sigma squared at the origin.
-- source:
--   Gaussian Lévy–Khintchine Esscher Volterra identity, previously formally Proved as gaussian_esscher_canonical_volterra_identity_of_positive_sigma; direct witness extraction.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_native_levy_esscher_double_tail_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_canonical_volterra_identity_of_positive_sigma
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
/-- The native Gaussian coefficient sigma squared over two appears explicitly in the causal scale equation. -/
theorem gaussian_esscher_volterra_native_variance_coefficient
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ∃ (β : ℝ) (K : ℝ → ℝ),
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      ∀ x : ℝ, 0 < x →
        (X.σ ^ 2 / 2) * V x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * V s ∂volume) = x := by
  sorry
end AvramDividend.Classical
