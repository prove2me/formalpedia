-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB220_original_selected_clipped_two_mesh_L2_cauchy
-- name    : AvramDividend.Classical.avram_gbB220_original_selected_clipped_two_mesh_L2_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:33:37.4822+00:00
-- url     : https://prove2.me/theorems/bef62c18-df63-4c9e-9718-d9a477672a0d
-- title:
--   Original stopped postpayment Gaussian selected-clipping coefficients are two-mesh L2 Cauchy for every countable horizon
-- statement:
--   For the original zero-jump controlled source, genuine postpayment dividends and any countable family of measurable stopping horizons, freely choose two clipping levels from separated open bands so that the expected time-integrated squared difference of two arbitrarily fine uniform meshes tends to zero under the simultaneous directed mesh filter.
-- source:
--   Proved original Gaussian selected-boundary B216 single-mesh L2 limit, B215 uniform measurability/amplitude and B219 finite physical-time nested L2 common-limit to two-mesh Cauchy.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB220_original_selected_clipped_two_mesh_L2_cauchy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ → ℕ) (hn : ∀ k, 0 < n k)
    (ρ : ℕ → Ω → ℝ≥0) (hρ : ∀ k, Measurable (ρ k))
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
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
    ∃ a ∈ Ioo alo ahi, ∃ b ∈ Ioo blo bhi,
      ∀ k : ℕ,
        Tendsto (fun mp : ℕ × ℕ =>
          ∫ t in Ioo (0 : ℝ) ((n k : ℕ) : ℝ),
            (∫ ω, (K a b k mp.1 t ω - K a b k mp.2 t ω)^2 ∂P)
            ∂volume) atTop (𝓝 (0 : ℝ)) := by sorry
