-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys20_original_stopped_sixterm_one_H_E_ledger_ae
-- name    : AvramDividend.Classical.avram_bv_phys20_original_stopped_sixterm_one_H_E_ledger_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T19:36:21.899438+00:00
-- url     : https://prove2.me/theorems/7435ab27-31cb-4aec-a27c-402abc0aad34
-- title:
--   One canonical H and E for the original stopped BV discounted cash and terminal ledger
-- statement:
--   On the same original X/D ruin/horizon-clipped physical grid, the initial right dividend, all stopped half-open discounted cash cells and post-right terminal are exactly the sum of one fixed original drift-plus-jump source H and one fixed four-part contact/Taylor/discount/payment error E, with the initial post-right reserve carried explicitly. Both H and E refer to the same path, grid, jump sums and time-zero atom; this is a deterministic finite-mesh identity, not yet an L1 or mean-zero limit.
-- source:
--   Direct algebraic regrouping of the authoritative Proved d51199a8 six-term original stopped cash/terminal identity. Intended as single H/E interface for the source-exact Open 2bc848f9 and 4f605d76.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_discounted_C1_six_term_stopped_physical_grid_identity
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys20_original_stopped_sixterm_one_H_E_ledger_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω) (T : ℝ≥0) (m : ℕ) :
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
      ((∑ i ∈ Finset.range (m + 1), cash i) +
        e (m + 1) * post (m + 1) - e 0 * post 0) =
      rightLimit D 0 ω + H + E := by sorry
