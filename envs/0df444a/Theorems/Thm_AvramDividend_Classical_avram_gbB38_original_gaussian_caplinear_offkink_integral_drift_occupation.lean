-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB38_original_gaussian_caplinear_offkink_integral_drift_occupation
-- name    : AvramDividend.Classical.avram_gbB38_original_gaussian_caplinear_offkink_integral_drift_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:41:43.6481+00:00
-- url     : https://prove2.me/theorems/9a3be44a-7fc1-4986-a26a-a040bfa3ae11
-- title:
--   Original pure-Gaussian caplinear HJB time drift is bounded by upper-strip occupation cost
-- statement:
--   For any positive reserve trajectory spending zero time at the interior clipping level, the expected or pathwise time integral of the discounted cap-linear Gaussian generator drift is bounded by the upper-strip occupation cost max(c,0). This supplies the generator drift component of the original finite-cap stopped Ito-Stieltjes cash inequality, conditional only on integrability and the required zero-level occupation.
-- source:
--   Integrate B35 off-kink HJB bound against a time measure using integral_mono_ae. Zero occupation of the clipping point is explicitly assumed almost everywhere and has separate Proved Gaussian local occupation support.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB35_original_gaussian_caplinear_offkink_HJB_drift_envelope
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB38_original_gaussian_caplinear_offkink_integral_drift_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (w : ℝ → ℝ) (b q : ℝ) (hq : 0 ≤ q) (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0)
    (μ : Measure ℝ) (Y : ℝ → ℝ)
    (hPos : ∀ᵐ t ∂μ, 0 < Y t)
    (hNoKink : ∀ᵐ t ∂μ, Y t ≠ b) :
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    Integrable (fun t => X.generator V (Y t) - q * V (Y t)) μ →
    Integrable (fun t => if b < Y t then max X.c 0 else 0) μ →
    (∫ t, X.generator V (Y t) - q * V (Y t) ∂μ) ≤
      (∫ t, if b < Y t then max X.c 0 else 0 ∂μ) := by sorry
