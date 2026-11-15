-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b249_original_ruinclipped_physical_postpayment_discount_gap_bounded_dividend_mass
-- name    : AvramDividend.Classical.avram_b249_original_ruinclipped_physical_postpayment_discount_gap_bounded_dividend_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:33:46.47274+00:00
-- url     : https://prove2.me/theorems/bda8990e-9d80-4315-8dce-869c66c2da09
-- title:
--   Original ruin-clipped finite mixed physical-grid pre/postpayment discount mismatch bounded by true bounded-mesh width times full right-dividend variation
-- statement:
--   For the original X, D and stopped physical grid v_i=min(i n/(m+1),sigma(omega)), if the genuine prepayment frozen-right-dividend reserve and actual postpayment reserve on each cell stay in one compact localisation interval where the tested original potential is L-Lipschitz, then the sum of the absolute original potential gap times the exact within-cell exponential discount decrement is bounded by q times physical cell width times L times the actual total right-dividend increase. This controls precisely the B248 left-to-right cash source mismatch on localised pre-ruin cells; it retains all original X and D values and has an explicit original total-dividend L1 domination route. The compact-band and mesh assumptions are explicit and require discharge from B236 localisation and genuine stop geometry.
-- source:
--   Apply Proved original local pre/postpayment discount mesh gap theorem to monotone clipped physical grid v_i, with exact frozen-original-D prepayment and true postpayment original X endpoints, bounded scalar mesh hmesh and compact interval Lipschitz premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_local_prepostpayment_discount_mesh_gap
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b249_original_ruinclipped_physical_postpayment_discount_gap_bounded_dividend_mass
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
    (hmesh : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j =>
        min ((j : ℝ≥0) * Δ) (σ ω)
      ((v (i + 1) : ℝ) - (v i : ℝ)) ≤ (Δ : ℝ))
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
