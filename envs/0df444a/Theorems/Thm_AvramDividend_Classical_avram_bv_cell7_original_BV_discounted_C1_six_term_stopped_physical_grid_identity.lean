-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_discounted_C1_six_term_stopped_physical_grid_identity
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_discounted_C1_six_term_stopped_physical_grid_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:51:29.50147+00:00
-- url     : https://prove2.me/theorems/d51199a8-9fe3-427d-beee-21ddee90b0dd
-- title:
--   Original discounted stopped BV cash plus terminal is exactly its six raw C1 physical cell terms and time-zero right dividend
-- statement:
--   For the actual bounded-variation spectrally negative Levy process X and its original dividend strategy D on the ruin/horizon clipped physical grid, the exact full discounted cash plus pre-right-payment terminal C1 chain identity holds pathwise with the time-zero right dividend added explicitly. The source terms are the actual continuous-component derivative increments, aggregate negative jump value changes, jump/continuous cross commutator, C1 Taylor remainder, discount commutator and payment remainder over the complete finite half-open stopped physical grid including the last contact cell. This is the source-exact physical specialisation of the independently Proved six-term original discounted identity bab12de9, isolating the necessary discount-weighted raw source for comparison against the newly Proved original compensated H physical grid rather than relying on the coarser undiscounted cap-extension inequality.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_full_cash_Y_J_C1_commutator_identity

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_discounted_C1_six_term_stopped_physical_grid_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (T : ℝ≥0) (m : ℕ) :
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
    rightLimit D 0 ω +
      ((∑ i ∈ Finset.range (m + 1), cash i) +
        e (m + 1) * post (m + 1) - e 0 * post 0) =
      rightLimit D 0 ω +
      ((∑ i ∈ Finset.range (m + 1),
         e i * (deriv w (z i) * c i)) +
       (∑ i ∈ Finset.range (m + 1),
         e i * (w (z i - j i) - w (z i))) +
       (∑ i ∈ Finset.range (m + 1),
         e i * (w (z i + c i - j i) - w (z i + c i) -
           w (z i - j i) + w (z i))) +
       (∑ i ∈ Finset.range (m + 1),
         e i * (w (z i + c i) - w (z i) - deriv w (z i) * c i)) +
       (∑ i ∈ Finset.range (m + 1),
         (e (i + 1) - e i) * post (i + 1)) +
       (∑ i ∈ Finset.range (m + 1), rem i)) := by sorry
