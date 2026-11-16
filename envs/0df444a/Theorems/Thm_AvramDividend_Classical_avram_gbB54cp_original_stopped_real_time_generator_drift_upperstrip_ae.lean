-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_original_stopped_real_time_generator_drift_upperstrip_ae
-- name    : AvramDividend.Classical.avram_gbB54cp_original_stopped_real_time_generator_drift_upperstrip_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:10:22.247595+00:00
-- url     : https://prove2.me/theorems/9a6ad576-ecca-4a2e-aa47-11ddaac154c4
-- title:
--   Original stopped finitecap Gaussian drift integral is bounded by true upper-strip occupation
-- statement:
--   For the true original right-limit dividend reserve on the exact bounded pre-stop real-time interval, Gaussian occupation nullity and the pre-stop postpayment reserve floor supply the a.e. nonzero-reserve and off-upper-kink hypotheses. The proved off-kink caplinear HJB generator inequality then bounds the true stopped drift integral by max(c,0) times upper-strip occupation under its two explicit integrability hypotheses. This is a source-faithful stochastic HJB drift component of the B54cp stopped Ito cash verification, without Brownian substitution or assuming no-kink occupancy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB54cp_original_stopped_real_time_generator_drift_upperstrip_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (b : ℝ)
    (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ᵐ ω ∂P,
      let S : Set ℝ := {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
      let μ : Measure ℝ := volume.restrict S
      let Y : ℝ → ℝ := fun t =>
        x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
      let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
      Integrable (fun t => X.generator V (Y t) - q * V (Y t)) μ →
      Integrable (fun t => if b < Y t then max X.c 0 else 0) μ →
      (∫ t, X.generator V (Y t) - q * V (Y t) ∂μ) ≤
        (∫ t, if b < Y t then max X.c 0 else 0 ∂μ) := by sorry
