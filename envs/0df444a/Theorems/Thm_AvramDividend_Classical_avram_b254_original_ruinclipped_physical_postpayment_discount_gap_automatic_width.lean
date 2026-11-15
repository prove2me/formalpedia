-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b254_original_ruinclipped_physical_postpayment_discount_gap_automatic_width
-- name    : AvramDividend.Classical.avram_b254_original_ruinclipped_physical_postpayment_discount_gap_automatic_width
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:44:04.404331+00:00
-- url     : https://prove2.me/theorems/705da1e7-3f88-4632-9d7d-d4e22710f0ab
-- title:
--   Original ruin-clipped mixed stopped physical-grid pre/post dividend discount mismatch bounded automatically by n/(m+1) times true dividend increase
-- statement:
--   For the actual original mixed source X, admissible dividend D and true clipped stopping mesh v_i=min(i n/(m+1),sigma(omega)), assume the original frozen prepayment and actual postpayment reserves on each source cell remain in the compact interval where tested potential w is L-Lipschitz. Then the total physical within-cell exponential discount decrement weighted by the original potential drop is bounded by q n/(m+1) L times the genuine total right-dividend variation. The actual physical width bound is automatic from the stopped-grid geometry B250; no separate mesh hypothesis is required. This is a source-faithful L1 error envelope for B236 original ruin-clipped Itô cash derivation, conditional only on B236 localisation ensuring compact reserve cells.
-- source:
--   Instantiate Proved original B249 discounted pre/post dividend frozen original rightLimit D gap bound, discharging its single deterministic physical mesh width assumption by Proved B250 true clipped stopped clock width.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b249_original_ruinclipped_physical_postpayment_discount_gap_bounded_dividend_mass
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b254_original_ruinclipped_physical_postpayment_discount_gap_automatic_width
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (a b : ℝ) (hLip :
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        |w s - w t| ≤ L * |s - t|)
    (σ : Ω → ℝ≥0) (n m : ℕ)
    (hPre : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j =>
        min ((j : ℝ≥0) * Δ) (σ ω)
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω ∈ Icc a b)
    (hPost : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j =>
        min ((j : ℝ≥0) * Δ) (σ ω)
      x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω ∈ Icc a b) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    (∑ i ∈ Finset.range m,
      (Real.exp (-(q * (v i : ℝ))) -
       Real.exp (-(q * (v (i + 1) : ℝ)))) *
      |w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
       w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω)|) ≤
    q * (Δ : ℝ) * L *
      (rightLimit D (v m) ω - rightLimit D (v 0) ω) := by sorry
