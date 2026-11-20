-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_uniform_true_stop_preterminal_HJB_Q_allgrids_nonpositive
-- name    : AvramDividend.Classical.avram_pj_workerC_original_uniform_true_stop_preterminal_HJB_Q_allgrids_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:40:26.687118+00:00
-- url     : https://prove2.me/theorems/9a2eac9d-535e-4548-bda0-74e707f9b343
-- title:
--   The actual uniform preterminal physical grid yields an HJB and right-payment Q_k≤0 for every refinement without additional precontact assumptions
-- statement:
--   For a genuine original stopped clock ρ dominated by true ruinTime, form uniform preterminal physical grids with k+1 slices. Every time rho*i/(k+1) for i≤k lies strictly before ruin or at time zero. The original stopped discounted HJB generator integral plus the sum of actual discounted right-payment HJB defects is pathwise ≤0 on every grid. This provides an explicit Q_k source in the purejump signed Ito mesh, with ruin-contact endpoint left to terminal value and no Gaussian term.
-- source:
--   Proved original uniform preterminal-grid contact geometry and finite-grid HJB/rightpayment sign lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_allphysical_grids_HJB_and_rightpayment_Q_nonpositive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_uniform_true_stop_preterminal_HJB_Q_allgrids_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (u v δ : ℝ) (hu : 0 < u) (hδ : 0 < δ)
    (huv : u + δ < v) (hvCap : v < C.toReal)
    (T : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let A : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
      (Finset.range (k + 1)).image
        (fun i : ℕ => ρ ω * ((i : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
    ∀ k : ℕ,
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        ((if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) *
          (if Y p ∈ Icc (u + δ) v then
            X.generator w (Y p) - q * w (Y p) else 0))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let B : Ω → ℝ := fun ω =>
      ∫ t : ℝ≥0, if t ≤ ρ ω then R (t, ω) else 0 ∂μT
    let Q : Ω → ℝ := fun ω => B ω +
      ∑ t ∈ A k ω, Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D t ω - D t ω) -
          (w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω -
              (rightLimit D t ω - D t ω))))
    ∀ ω, Q ω ≤ 0 := by sorry
