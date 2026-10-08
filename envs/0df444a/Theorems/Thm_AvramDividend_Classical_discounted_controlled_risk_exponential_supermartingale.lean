-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_controlled_risk_exponential_supermartingale
-- name    : AvramDividend.Classical.discounted_controlled_risk_exponential_supermartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:13:55.490475+00:00
-- url     : https://prove2.me/theorems/493fec86-f770-4c77-86f9-e1909783cba4
-- title:
--   Initial-capital controlled risk process has q-discounted exponential supermartingale
-- statement:
--   For the true controlled reserve U_t=x+X_t−D_t defined by the Avram dividend model, θ≥0 and q≥ψ(θ), the process e^(θ U_t−qt) is a supermartingale for every dividend strategy D. From the previously authored and formalised controlled exponential supermartingale of X_t−D_t, multiply by the nonnegative constant e^(θx), then apply the exponential addition identity and the definition of riskProcess. This is an exponential-test verification property and does not yet incorporate total discounted dividend payments.
-- source:
--   Theorem discounted_controlled_levy_exponential_supermartingale and pinned Mathlib Supermartingale.smul_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_controlled_risk_exponential_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q) :
    Supermartingale (fun t ω =>
      Real.exp (θ * riskProcess X x D t ω - (t : ℝ) * q)) 𝓕 P := by sorry
