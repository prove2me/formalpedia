-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_levy_single_contact_raw_residual
-- name    : AvramDividend.Classical.avram_bv_strict12_original_levy_single_contact_raw_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:09:25.568405+00:00
-- url     : https://prove2.me/theorems/aa8e8474-ec43-4e06-b0c1-fda9cddc285f
-- title:
--   Original Lévy intrinsic BV residual is ruin-clipped plus one contact cell
-- statement:
--   Specialises the algebraically exact at-most-one-contact-cell certificate to the original SpectrallyNegativeLevy process X and its intrinsic raw drift-minus-path-minus-jump-series residual R. This is a direct source-exact bridge for the BV physical-grid two-scale proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict12_original_levy_single_contact_raw_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (n : ℕ) (u : ℕ → ℝ≥0) (τ : ℝ≥0)
    (W : ℕ → ℝ) (E : ℕ → Prop) (hmono : Monotone u)
    (hE : ∀ i, E i → u i < τ) :
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
    let Raw := ∑ i ∈ Finset.range n,
      if E i then W i * (R (u i) - R (u (i + 1))) else 0
    let Stopped := ∑ i ∈ Finset.range n,
      if E i then W i * (R (min (u i) τ) - R (min (u (i + 1)) τ)) else 0
    ∃ t : ℝ, Raw = Stopped + t ∧
      (t = 0 ∨ ∃ i ∈ Finset.range n,
        E i ∧ τ < u (i + 1) ∧
          t = W i * (R τ - R (u (i + 1)))) := by sorry
