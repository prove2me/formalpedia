-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_bounded_stopped_discount_cash_mesh_absolute_error_L1_eventual
-- name    : AvramDividend.Classical.avram_pj_workerC_original_bounded_stopped_discount_cash_mesh_absolute_error_L1_eventual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:34:41.496905+00:00
-- url     : https://prove2.me/theorems/0c5ef385-5292-43a7-b6d2-cfdec60e1cd7
-- title:
--   Actual bounded stopped strict dividend cash mesh error has eventually arbitrarily small genuine L1 absolute norm
-- statement:
--   For the true original stopped ruin-dominated Lévy dividend strategy, the clipped finite-horizon discounted cash grid error E_m is nonnegative pathwise (qΔ paid cash plus discounted right-end mesh tail). The already-Proved expected E_m epsilon estimate therefore upgrades to a genuine absolute L1 estimate: eventually ∫|E_m| ≤ epsilon, with Integrable E_m. This supplies an actual Stieltjes cash component of the E_k error in the purejump signed physical Ito source and preserves the paymentTimes/Iio endpoint.
-- source:
--   Public Proved 0b0c563c original bounded-stop discounted Stieltjes cash mesh error L1, and positivity of qΔ, dividend measure and discount weights.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger39_original_bounded_stop_discount_mesh_error_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_bounded_stopped_discount_cash_mesh_absolute_error_L1_eventual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let u : ℝ≥0 := ρ ω - Δ
      q * (Δ : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo (u : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (E m) P ∧ (∫ ω, |E m ω| ∂P) ≤ ε := by sorry
