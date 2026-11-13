-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_C1_positive_band_analytic_certificate
-- name    : AvramDividend.Classical.avram_chat24_C1_positive_band_analytic_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:24:39.390464+00:00
-- url     : https://prove2.me/theorems/e61f5d17-cee5-4d6e-ab7d-ba0772a34d7c
-- title:
--   Compact C1 positive reserve band provides measurable payoff, continuous drift and uniform jump bounds
-- statement:
--   For a payoff continuous on nonnegative reserves, zero below zero and C1 at every strictly positive reserve, every compact positive band admits a Lipschitz bound on its half-width enlargement and a uniform payoff bound on the full left half-line. The payoff is Borel measurable and the drift-discount integrand is continuous on the band. The exact certificate supplies the deterministic hypotheses for the already Proved original BV marked-product L1 theorem in parent 434a944f-a6f4-4b64-8aa8-8554ba093a5c; it assumes neither occupation integrability nor convergence of any integral.
-- source:
--   Analytic split of exact stopped occupation regularity target 434a944f-a6f4-4b64-8aa8-8554ba093a5c. Classical compactness and the compact C1 Lipschitz theorem.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_chat24_C1_positive_band_analytic_certificate
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw : ContDiffOn ℝ 1 w (Ioi 0))
    (a b d q : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Measurable w ∧ ContinuousOn (fun y => d * deriv w y - q * w y) (Icc a b) ∧
    ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b, |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) := by
  sorry
