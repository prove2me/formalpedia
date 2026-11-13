-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB207_original_selected_clipped_mesh_L2_for_countable_horizons
-- name    : AvramDividend.Classical.avram_gbB207_original_selected_clipped_mesh_L2_for_countable_horizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:34:30.368947+00:00
-- url     : https://prove2.me/theorems/bfdc384c-4a55-4324-af3d-f16591d84b39
-- title:
--   Existential good clipping boundaries give original postpayment stopped Gaussian coefficient physical L2 mesh convergence for every horizon
-- statement:
--   Under joint measurable and finite bounded coefficients for all candidate interior clipping boundaries, select a lower and upper cutoff in prescribed separated intervals so that the original zero-jump Gaussian controlled postpayment step coefficients converge in integrated probability-and-time square mean to their exact physical-time stopped limits, for every countably indexed horizon.
-- source:
--   Original Gaussian B alternate finite-cap L2 mesh convergence route without B100 universal fixed-level occupation: combines Proved B205 and generic bounded L2 limit B157.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB207_original_selected_clipped_mesh_L2_for_countable_horizons
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ → ℕ) (hn : ∀ k, 0 < n k)
    (ρ : ℕ → Ω → ℝ≥0) (q : ℝ) (w : ℝ → ℝ)
    (alo ahi blo bhi : ℝ) (ha : alo < ahi)
    (hSep : ahi < blo) (hb : blo < bhi)
    (hDeriv : ∀ y ∈ Ioo alo bhi, ContinuousAt (deriv w) y) :
    let Y : ℝ≥0 → Ω → ℝ := fun s ω =>
      x + X.X s ω - rightLimit D s ω
    let K : ℝ → ℝ → ℕ → ℕ → ℝ → Ω → ℝ := fun a b k m t ω =>
      let Δ : ℝ≥0 := ((n k : ℕ) : ℝ≥0) /
        ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ) then
          if (s : ℝ) < (ρ k ω : ℝ) then
            Real.exp (-(q * (s : ℝ))) *
              (if Y (Real.toNNReal (s : ℝ)) ω ∈ Icc a b
                then deriv w (Y (Real.toNNReal (s : ℝ)) ω)
                else 1)
          else 0
        else 0)
    let H : ℝ → ℝ → ℕ → ℝ → Ω → ℝ := fun a b k t ω =>
      if t < (ρ k ω : ℝ) then
        Real.exp (-(q * t)) *
          (if Y (Real.toNNReal t) ω ∈ Icc a b
            then deriv w (Y (Real.toNNReal t) ω)
            else 1)
      else 0
    (∀ a ∈ Ioo alo ahi, ∀ b ∈ Ioo blo bhi,
      ∀ k m, Measurable (fun z : ℝ × Ω =>
        K a b k m z.1 z.2)) →
    (∀ a ∈ Ioo alo ahi, ∀ b ∈ Ioo blo bhi,
      ∀ k, Measurable (fun z : ℝ × Ω =>
        H a b k z.1 z.2)) →
    (∀ a ∈ Ioo alo ahi, ∀ b ∈ Ioo blo bhi,
      ∀ k, ∃ BK BH : ℝ, 0 ≤ BK ∧ 0 ≤ BH ∧
        (∀ m t ω, t ∈ Ioo (0 : ℝ) ((n k : ℕ) : ℝ) →
          |K a b k m t ω| ≤ BK) ∧
        (∀ t ω, t ∈ Ioo (0 : ℝ) ((n k : ℕ) : ℝ) →
          |H a b k t ω| ≤ BH)) →
    ∃ a ∈ Ioo alo ahi, ∃ b ∈ Ioo blo bhi,
      ∀ k : ℕ,
        Tendsto (fun m : ℕ =>
          ∫ t in Ioo (0 : ℝ) ((n k : ℕ) : ℝ),
            (∫ ω, (K a b k m t ω - H a b k t ω)^2 ∂P)
            ∂volume) atTop (𝓝 (0 : ℝ)) := by sorry
