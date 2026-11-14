-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB238_fixed_clipped_physical_mesh_two_level_null_occupation_L2_cauchy
-- name    : AvramDividend.Classical.avram_gbB238_fixed_clipped_physical_mesh_two_level_null_occupation_L2_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:43:34.569539+00:00
-- url     : https://prove2.me/theorems/088f85c2-7397-46e0-bbd6-7ff95d6003f8
-- title:
--   Fixed two-level null occupation and compact clipped-gradient regularity yield physical-time two-mesh L2 Cauchy
-- statement:
--   An arbitrary jointly measurable nonnegative-time process with almost surely countably many path discontinuities, two fixed clipping levels of zero physical-time occupation, a bounded closed-band continuous clipped derivative and interior differentiability, and measurable random stopping horizon has genuine discounted physical-time uniform meshes that are two-mesh Cauchy in integrated expected square. This uses the exact same grid coefficient as B65, conditional only on the two prescribed level occupations.
-- source:
--   Original Gaussian fixed-cutoff B65 closest generic bridge from proved B206 + B215 + B219; B100 provides full-time prescribed level null occupancy when its arbitrary stopping clock is set to deterministic n.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB238_fixed_clipped_physical_mesh_two_level_null_occupation_L2_cauchy
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (Y : ℝ≥0 → Ω → ℝ)
    (hY : Measurable (fun z : ℝ≥0 × Ω => Y z.1 z.2))
    (hCount : ∀ᵐ ω ∂P,
      Set.Countable {s : ℝ≥0 |
        ¬ ContinuousAt (fun u : ℝ≥0 => Y u ω) s})
    (n : ℕ) (hn : 0 < n) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (a b : ℝ) (ρ : Ω → ℝ≥0)
    (hρ : Measurable ρ)
    (hOccA : ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧
        Y (Real.toNNReal t) ω = a} = 0)
    (hOccB : ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧
        Y (Real.toNNReal t) ω = b} = 0)
    (hDeriv : ∀ y ∈ Set.Ioo a b,
      ContinuousAt (deriv w) y)
    (hClosed : ContinuousOn (deriv w) (Set.Icc a b)) :
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ)
        then if (s : ℝ) < (ρ ω : ℝ) then
          Real.exp (-(q * (s : ℝ))) *
            (if Y (Real.toNNReal (s : ℝ)) ω ∈ Set.Icc a b
              then deriv w (Y (Real.toNNReal (s : ℝ)) ω) else 1)
        else 0 else 0)
    Tendsto (fun mp : ℕ × ℕ =>
      ∫ t in Set.Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (K mp.1 t ω - K mp.2 t ω)^2 ∂P) ∂volume)
      atTop (𝓝 (0 : ℝ)) := by sorry
