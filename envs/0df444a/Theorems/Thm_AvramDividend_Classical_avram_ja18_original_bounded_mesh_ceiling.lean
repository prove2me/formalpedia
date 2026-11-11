-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_bounded_mesh_ceiling
-- name    : AvramDividend.Classical.avram_ja18_original_bounded_mesh_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T21:17:31.718965+00:00
-- url     : https://prove2.me/theorems/1d01e41f-3949-45d9-9ae6-9f9aaffdaa16
-- title:
--   Physical original stopping clock admits a bounded sampled-martingale grid ceiling within one mesh
-- statement:
--   A bounded true stopping clock on the original right-continuous filtration can be rounded upwards on any monotone deterministic grid with step size bounded by delta. The least covering index is a bounded stopping time for the sampled filtration; its sampled time is between the original stop and delta above it. This is the exact clock-approximation interface for optional sampling.
-- source:
--   General source-exact 71-line finite12_general_ceiling_v2.lean, made public to support 2d92580d. Nat.find minimisation plus physical stop events; no assumptions about independent Brownian noise or mark moments.

import Mathlib
import Mathlib.Data.Nat.Find
import Mathlib.Probability.Process.Stopping
open MeasureTheory
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_bounded_mesh_ceiling
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : ∀ ω, σ ω ≤ e N)
    (δ : ℝ≥0) (h0 : e 0 = 0)
    (hStep : ∀ i, e (i + 1) ≤ e i + δ)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ)) :
    ∃ K : Ω → ℕ,
      IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ)) ∧
      (∀ ω, (K ω : WithTop ℕ) ≤ (N : WithTop ℕ)) ∧
      (∀ ω, σ ω ≤ e (K ω) ∧ e (K ω) ≤ σ ω + δ) := by sorry
