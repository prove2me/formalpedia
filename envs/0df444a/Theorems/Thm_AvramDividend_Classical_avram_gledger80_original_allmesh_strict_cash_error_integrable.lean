-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger80_original_allmesh_strict_cash_error_integrable
-- name    : AvramDividend.Classical.avram_gledger80_original_allmesh_strict_cash_error_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:31:25.470416+00:00
-- url     : https://prove2.me/theorems/05a4d601-af4d-4e5b-a720-a78d54b587b6
-- title:
--   Every original discounted strict stopped cash mesh error is integrable
-- statement:
--   For every fixed deterministic mesh, the explicitly weighted strict pre-stop dividend cash and the final strict open mesh strip each have finite L1 expectation under original X and D on bounded stopping clocks. This removes the eventual-mesh quantifier from Proved gledger42 for the integrability part only; it is needed for the Gaussian cash residual dominated by the same E_m.
-- source:
--   Direct extract of accepted gledger42 6be8347d source. Original strict full F has integrable envelope; strict last-cell T is integrable for every real strip width, and the sum is integrable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gledger80_original_allmesh_strict_cash_error_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let F : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (n : ℝ)) * F + T
    ∀ m : ℕ, Integrable (E m) P := by sorry
