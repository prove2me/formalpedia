-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB215_generic_physical_clipped_mesh_measurable_bounded
-- name    : AvramDividend.Classical.avram_gbB215_generic_physical_clipped_mesh_measurable_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:15:50.693899+00:00
-- url     : https://prove2.me/theorems/8aef8314-8533-4b1d-b98b-79e892931c53
-- title:
--   Generic compact-clipped physical-time mesh coefficients are jointly measurable and uniformly bounded
-- statement:
--   For an arbitrary jointly measurable reserve path, a measurable random stop and a derivative continuous on the compact clipping interval, the stopped discounted uniform-grid physical-time coefficients and their stopped continuous-time limit are jointly measurable and uniformly bounded on a finite time horizon.
-- source:
--   Gaussian B207 selected clipping convergence: discharge its measurable and bounded coefficient assumptions using existing Proved B210 B211 B212 B213 and B209 B214.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB215_generic_physical_clipped_mesh_measurable_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℝ)
    (hY : Measurable (fun z : ℝ≥0 × Ω => Y z.1 z.2))
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (w : ℝ → ℝ) (a b : ℝ)
    (hc : ContinuousOn (deriv w) (Icc a b))
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
    let H : ℝ → Ω → ℝ := fun t ω =>
      if t < (ρ ω : ℝ) then
        Real.exp (-(q * t)) *
          (if Y (Real.toNNReal t) ω ∈ Icc a b
            then deriv w (Y (Real.toNNReal t) ω) else 1)
      else 0
    (∀ m, Measurable (fun z : ℝ × Ω => K m z.1 z.2)) ∧
    Measurable (fun z : ℝ × Ω => H z.1 z.2) ∧
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ m t ω, t ∈ Ioo (0 : ℝ) (n : ℝ) → |K m t ω| ≤ B) ∧
      (∀ t ω, t ∈ Ioo (0 : ℝ) (n : ℝ) → |H t ω| ≤ B) := by sorry
