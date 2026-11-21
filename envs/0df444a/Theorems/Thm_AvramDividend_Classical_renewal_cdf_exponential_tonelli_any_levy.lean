-- Prove2me | Theorems.Thm_AvramDividend_Classical_renewal_cdf_exponential_tonelli_any_levy
-- name    : AvramDividend.Classical.renewal_cdf_exponential_tonelli_any_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T18:44:27.731062+00:00
-- url     : https://prove2.me/theorems/89aae852-2bd3-4c04-8bca-b75278cdb59b
-- title:
--   Renewal cumulative-distribution Laplace identity for any spectrally negative Lévy exponent
-- statement:
--   For any spectrally negative Lévy exponent ψ and a positive-supported measure ν with finite cumulative mass and ∫exp(-θz)dν(z)=θ/ψ(θ) when ψ(θ)>0, the cumulative W(x)=ν((0,x]) has Laplace transform 1/ψ(θ) and is integrable against exp(-θx). This deterministic Tonelli identity does not require a nonzero Gaussian coefficient or the Standing assumption. Its proof specialises the already Proved 847548b4-661a-414b-994f-5b5a7b87dbf0, whose accepted source does not use either condition. Supports the purejump UBV zero-discount scale construction.
-- source:
--   Accepted Prove2Me theorem AvramDividend.Classical.avram_p4_f6_renewal_cdf_exponential_tonelli (847548b4-661a-414b-994f-5b5a7b87dbf0), accepted submission 4271de3c-ec98-44d9-ae71-5267a2edc224; exact proof with unused Gaussian/Standing hypotheses removed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.renewal_cdf_exponential_tonelli_any_levy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ν : Measure ℝ)
    (hSupp : ν (Iic (0 : ℝ)) = 0)
    (hFin : ∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤)
    (hLap : ∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y : ℝ => Real.exp (-(θ * y))) (Ioi 0) ν ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) ∂ν = θ / X.ψ θ) :
    ∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y : ℝ => Real.exp (-(θ * y)) * (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0)) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0) =
      (X.ψ θ)⁻¹ := by sorry
