-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB205_original_choose_good_levels_for_countable_mesh_limits
-- name    : AvramDividend.Classical.avram_gbB205_original_choose_good_levels_for_countable_mesh_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:24:14.394674+00:00
-- url     : https://prove2.me/theorems/9712effa-d456-4715-91fb-6687206c9b5f
-- title:
--   Choose two original reserve clipping boundaries giving almost-everywhere physical mesh convergence for every countable stopped horizon
-- statement:
--   For the original zero-jump Gaussian Lévy source and its real postpayment dividend process, every two separated open clipping intervals admit a lower and upper threshold for which the exact discounted uniform-mesh coefficient converges at almost every time on an almost-sure event for every member of any prescribed countable stopping-horizon family, provided the gradient is continuous across the containing band.
-- source:
--   Alternative original Gaussian finite-cap approach to B102/B116, avoiding universal fixed-level occupation B100 by selecting good clipping boundaries and applying B202,B203,B204.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB205_original_choose_good_levels_for_countable_mesh_limits
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
    ∃ a : ℝ, a ∈ Ioo alo ahi ∧
    ∃ b : ℝ, b ∈ Ioo blo bhi ∧
      ∀ k : ℕ, ∀ᵐ ω ∂P,
        ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) ((n k : ℕ) : ℝ))),
          Tendsto (fun m : ℕ =>
            let Δ : ℝ≥0 := ((n k : ℕ) : ℝ≥0) /
              ((m + 1 : ℕ) : ℝ≥0)
            (Finset.range (m + 1)).sum (fun i =>
              let s : ℝ≥0 := (i : ℝ≥0) * Δ
              if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ)
              then if (s : ℝ) < (ρ k ω : ℝ) then
                Real.exp (-(q * (s : ℝ))) *
                  (if Y (Real.toNNReal (s : ℝ)) ω ∈ Icc a b
                    then deriv w (Y (Real.toNNReal (s : ℝ)) ω)
                    else 1)
              else 0 else 0)) atTop
            (𝓝 (if t < (ρ k ω : ℝ) then
              Real.exp (-(q * t)) *
                (if Y (Real.toNNReal t) ω ∈ Icc a b
                  then deriv w (Y (Real.toNNReal t) ω)
                  else 1)
              else 0)) := by sorry
