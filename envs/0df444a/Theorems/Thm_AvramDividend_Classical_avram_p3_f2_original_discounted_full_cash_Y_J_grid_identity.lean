-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_full_cash_Y_J_grid_identity
-- name    : AvramDividend.Classical.avram_p3_f2_original_discounted_full_cash_Y_J_grid_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:54:48.62961+00:00
-- url     : https://prove2.me/theorems/7b98c140-827e-4985-ac4d-9c36f66c835a
-- title:
--   Exact original discounted Stieltjes dividend cash and terminal product grid split into genuine Y and J source cells
-- statement:
--   Combine the already proved original discounted true-paymentTimes Stieltjes product grid with the exact source-frozen full-X to jump-removed-Y and negative-J cell identity. The resulting source-exact finite-grid equality retains the true original cash measure, post-rightpayment terminal, endpoint discount correction and explicit true dividend remainder while isolating the physical Y source increment and original negative-J value jump on each grid cell. This supplies a direct finite-grid change-of-variables starting identity for the canonical P3 signed stopped source chain, without assuming generator, compensation, drift sign, boundary localisation or expectation conclusions.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_exact_discounted_product_remainder_identity
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_frozen_X_cell_exact_Y_J_split
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_discounted_full_cash_Y_J_grid_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ) :
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
          Set.Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let frozen : ℕ → ℝ := fun i =>
      w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let rem : ℕ → ℝ := fun i =>
      cash i + e i * (post (i + 1) - post i - frozen i)
    (∑ i ∈ Finset.range n, cash i) +
      e n * post n - e 0 * post 0 =
      (∑ i ∈ Finset.range n, e i *
        ((w (z i + c i - j i) - w (z i - j i)) +
         (w (z i - j i) - w (z i)))) +
      (∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1)) +
      ∑ i ∈ Finset.range n, rem i := by sorry
