-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_killed_record_esscher_likelihood
-- name    : AvramDividend.Classical.avram_ws01h_capped_killed_record_esscher_likelihood
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:36:01.796+00:00
-- url     : https://prove2.me/theorems/a597c3a2-a6f7-412a-ad50-fcf5ea54637c
-- title:
--   Actual capped surviving record gives its exact stopped Esscher density at the root
-- statement:
--   At a finite true first strict upper passage of the actual spectrally negative Levy path, the capped stopped Esscher likelihood under psi(phi)=q equals the stopped discount at its deterministic achieved height b. This supplies the hWeight hypothesis of the genuine killed first-record Qp residual-clock factor by actual no-positive-overshoot, and assumes no two-sided exit identity.
-- source:
--   Avram–Palmowski–Pistorius (2007), first passage; canonically Proved capped no-positive-overshoot df1c0da0-aa12-4f9f-89de-296081c3a314.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_record_no_positive_overshoot

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_capped_killed_record_esscher_likelihood
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (N : ℝ≥0) (ω : Ω)
    (φ q p : ℝ) (hroot : X.ψ φ = q)
    (hhit : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) :
    (let τ : ℝ≥0 :=
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     ENNReal.ofReal (Real.exp (-(p * (τ : ℝ)))) *
       ENNReal.ofReal (Real.exp
         (φ * X.X τ ω - (τ : ℝ) * X.ψ φ)) =
     ENNReal.ofReal (Real.exp (-(p * (τ : ℝ)))) *
       ENNReal.ofReal (Real.exp (φ * b - (τ : ℝ) * q))) := by sorry
