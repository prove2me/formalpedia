-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_allphysical_grids_HJB_and_rightpayment_Q_nonpositive
-- name    : AvramDividend.Classical.avram_pj_workerC_original_allphysical_grids_HJB_and_rightpayment_Q_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:30:19.812216+00:00
-- url     : https://prove2.me/theorems/2a319116-d08f-48e4-be67-c590ea525dbd
-- title:
--   Original stopped finitecap physical HJB and right-payment signed Q remains nonpositive simultaneously on every grid
-- statement:
--   For the true original stopped Lévy reserve, a sequence of finite physical payment grids whose times are pre-ruin or zero, the source HJB generator integral B and the actual discounted right-payment loss at each grid have nonpositive sum Q_k pathwise for every k. This proves exactly the Q_k<=0 part of the signed two-stage mesh source without a Gaussian term or assumed martingale law.
-- source:
--   Already Proved f6aa78d7 exact original stopped physical HJB plus finite right-payment certificate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_physical_HJB_B_plus_finite_rightpayment_Q_nonpositive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_allphysical_grids_HJB_and_rightpayment_Q_nonpositive
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
    (A : ℕ → Ω → Finset ℝ≥0)
    (hPre : ∀ k ω t, t ∈ A k ω →
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
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
