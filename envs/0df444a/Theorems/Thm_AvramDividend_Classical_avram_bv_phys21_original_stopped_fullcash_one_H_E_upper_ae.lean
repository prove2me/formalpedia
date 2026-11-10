-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys21_original_stopped_fullcash_one_H_E_upper_ae
-- name    : AvramDividend.Classical.avram_bv_phys21_original_stopped_fullcash_one_H_E_upper_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T19:50:45.035525+00:00
-- url     : https://prove2.me/theorems/70dffe91-c3bf-4603-a7b0-4e62a4b9b9ce
-- title:
--   Full original stopped cash and terminal bounded by initial candidate plus the same H and E
-- statement:
--   The stopped half-open original dividend-measure cash, original horizon/ruin post-right terminal and initial right dividend are bounded pathwise by w(x) plus the SAME unaltered raw original X/D source H and four-piece error E of the exact stopped ledger. Uses the original time-zero jump secant, and correctly retains all pathwise contact atoms. No E-positive-L1 or H-centering claim.
-- source:
--   Original Proved 7435ab27 one H/E identity combined with Proved e6bfefd9 time-zero pre/post-payment atom bound. Necessary finite-mesh pathwise inequality toward physical c5ce01c6 and 2bc848f9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_discounted_C1_six_term_stopped_physical_grid_identity
import Theorems.Thm_AvramDividend_Classical_avram_bv_phys20_original_stopped_sixterm_one_H_E_ledger_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys21_original_stopped_fullcash_one_H_E_upper_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (T : ℝ≥0) (m : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let frozen : ℕ → ℝ := fun i =>
      w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let rem : ℕ → ℝ := fun i =>
      cash i + e i * (post (i + 1) - post i - frozen i)
    let H : ℝ :=
      (∑ i ∈ Finset.range (m + 1), e i * (deriv w (z i) * c i)) +
      (∑ i ∈ Finset.range (m + 1),
        e i * (w (z i - j i) - w (z i)))
    let E : ℝ :=
      (∑ i ∈ Finset.range (m + 1),
        e i * (w (z i + c i - j i) - w (z i + c i) -
          w (z i - j i) + w (z i))) +
      (∑ i ∈ Finset.range (m + 1),
        e i * (w (z i + c i) - w (z i) - deriv w (z i) * c i)) +
      (∑ i ∈ Finset.range (m + 1),
        (e (i + 1) - e i) * post (i + 1)) +
      (∑ i ∈ Finset.range (m + 1), rem i)
    rightLimit D 0 ω +
      (∑ i ∈ Finset.range (m + 1), cash i) +
        e (m + 1) * post (m + 1) ≤ w x + H + E := by sorry
