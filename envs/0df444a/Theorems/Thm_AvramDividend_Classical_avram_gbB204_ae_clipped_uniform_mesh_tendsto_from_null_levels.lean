-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB204_ae_clipped_uniform_mesh_tendsto_from_null_levels
-- name    : AvramDividend.Classical.avram_gbB204_ae_clipped_uniform_mesh_tendsto_from_null_levels
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:21:23.552248+00:00
-- url     : https://prove2.me/theorems/e86d30af-9861-4748-b9ab-673978bb5f3c
-- title:
--   Almost-everywhere convergence of original-type clipped Gaussian step coefficients at two occupation-null levels
-- statement:
--   For a regulated sample path with only countably many discontinuities and two clipping levels of null time occupation, the exact NNReal uniform-mesh discounted clipped coefficients converge almost surely for Lebesgue-almost every physical time to the stopped clipped continuous-time coefficient.
-- source:
--   Alternative Gaussian finitecap B102 route using chosen levels from B202, Proved B203 good time and B162 exact uniform mesh convergence; avoids assuming all prescribed cutoff levels are atomless.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB204_ae_clipped_uniform_mesh_tendsto_from_null_levels
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (Y : ℝ≥0 → Ω → ℝ)
    (hCount : ∀ᵐ ω ∂P,
      Set.Countable {s : ℝ≥0 | ¬ ContinuousAt
        (fun u : ℝ≥0 => Y u ω) s})
    (n : ℕ) (hn : 0 < n) (q : ℝ) (w : ℝ → ℝ)
    (a b : ℝ) (ρ : Ω → ℝ≥0)
    (hOccA : ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧
        Y (Real.toNNReal t) ω = a} = 0)
    (hOccB : ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧
        Y (Real.toNNReal t) ω = b} = 0)
    (hDeriv : ∀ y ∈ Ioo a b, ContinuousAt (deriv w) y) :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict
      (Ioo (0 : ℝ) (n : ℝ))),
      Tendsto (fun m : ℕ =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        (Finset.range (m + 1)).sum (fun i =>
          let s : ℝ≥0 := (i : ℝ≥0) * Δ
          if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ) then
            if (s : ℝ) < (ρ ω : ℝ) then
              Real.exp (-(q * (s : ℝ))) *
                (if Y (Real.toNNReal (s : ℝ)) ω ∈ Icc a b
                  then deriv w (Y (Real.toNNReal (s : ℝ)) ω)
                  else 1)
            else 0
          else 0)) atTop
        (𝓝 (if t < (ρ ω : ℝ) then
          Real.exp (-(q * t)) *
            (if Y (Real.toNNReal t) ω ∈ Icc a b
              then deriv w (Y (Real.toNNReal t) ω)
              else 1)
          else 0)) := by sorry
