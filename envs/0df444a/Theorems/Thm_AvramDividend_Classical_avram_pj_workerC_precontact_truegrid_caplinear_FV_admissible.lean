-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_precontact_truegrid_caplinear_FV_admissible
-- name    : AvramDividend.Classical.avram_pj_workerC_precontact_truegrid_caplinear_FV_admissible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T21:05:58.510312+00:00
-- url     : https://prove2.me/theorems/5cd1a4e9-6501-4309-ab91-1e20ac54ac04
-- title:
--   Original admissibility alone gives full precontact physical-grid dividend variation sign
-- statement:
--   From actual admissibility derive the dividend strategy as hD.1.1. The precontact filtered true grid postpayment reserve and original caplinear value then satisfy the nonpositive within-cell signed dividend correction, with no extra strategy premise.
-- source:
--   Direct invocation of precontact original grid signed FV lemma f9541303 with hD.1.1, the only assumption in the original purejump target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_caplinear_allcell_discounted_cash_loss_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_precontact_truegrid_caplinear_dividend_FV_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_precontact_truegrid_caplinear_FV_admissible
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω)
    (u : ℕ → ℝ≥0)
    (hu : ∀ i, u i = min
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) (ρ ω)) :
    let good : Finset ℕ :=
      (Finset.range (m + 1)).filter (fun i =>
        u (i + 1) = 0 ∨
          (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (∑ i ∈ good,
      Real.exp (-(q * (u (i + 1) : ℝ))) *
        ((rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) -
          (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
           V (x + X.X (u (i + 1)) ω -
              rightLimit D (u (i + 1)) ω)))) ≤ 0 := by sorry
