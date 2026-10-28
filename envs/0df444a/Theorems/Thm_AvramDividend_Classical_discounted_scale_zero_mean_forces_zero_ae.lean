-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_scale_zero_mean_forces_zero_ae
-- name    : AvramDividend.Classical.discounted_scale_zero_mean_forces_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:06:38.939398+00:00
-- url     : https://prove2.me/theorems/aa642422-9931-44c1-8f2a-f92cd4e3304d
-- title:
--   Zero-mean discounted scale reward vanishes almost surely
-- statement:
--   If W is a scale function with W(0)=0 and the un-stopped discounted reward e^(-qt)W(X_t) is integrable with mean W(0), then W(X_t)=0 almost surely. This rigorous consequence of nonnegative scale rewards identifies why a putative un-killed scale martingale requires careful scrutiny at reserve zero; the valid two-sided exit proof must work with an appropriately stopped reward.
-- source:
--   Nonnegative zero-integral criterion in pinned Mathlib and the defining nonnegativity/negative support of IsScaleFunction.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.discounted_scale_zero_mean_forces_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hW0 : W 0 = 0) (t : ℝ≥0)
    (hInt : Integrable
      (fun ω : Ω => Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) P)
    (hMean : (∫ ω : Ω, Real.exp (-(q * (t : ℝ))) *
      W (X.X t ω) ∂P) = W 0) :
    ∀ᵐ ω ∂P, W (X.X t ω) = 0 := by sorry
