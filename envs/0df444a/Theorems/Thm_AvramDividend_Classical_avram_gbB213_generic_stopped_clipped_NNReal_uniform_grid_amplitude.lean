-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB213_generic_stopped_clipped_NNReal_uniform_grid_amplitude
-- name    : AvramDividend.Classical.avram_gbB213_generic_stopped_clipped_NNReal_uniform_grid_amplitude
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:11:43.697484+00:00
-- url     : https://prove2.me/theorems/c9f2432f-3421-4049-bc1f-f7fb6fcde7bf
-- title:
--   Exact stopped clipped nonnegative-real uniform-grid coefficient sum has a global physical-time amplitude bound
-- statement:
--   For an arbitrary original-type state process, any measurable or nonmeasurable random stopping time and a gradient continuous on a chosen compact interval, every physical-time uniform NNReal grid step coefficient has a uniform nonnegative amplitude bound inside the finite positive horizon, independent of the mesh and sample path.
-- source:
--   Generic boundedness component for alternative original Gaussian selected clipping L2 convergence B207; Proved B212 one-coefficient bound and B146 real uniform grid one-active-cell property.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
open MeasureTheory Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB213_generic_stopped_clipped_NNReal_uniform_grid_amplitude
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ)
    (ρ : Ω → ℝ≥0) (w : ℝ → ℝ)
    (a b : ℝ) (hContinuous : ContinuousOn (deriv w) (Icc a b))
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (hn : 0 < n) :
    let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
        (if Y s ω ∈ Icc a b then deriv w (Y s ω) else 1)
      else 0
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ)
        then G m i ω else 0)
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m t ω,
      t ∈ Ioo (0 : ℝ) (n : ℝ) → |K m t ω| ≤ B := by sorry
