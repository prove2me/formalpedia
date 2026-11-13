-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b23_original_compact_preleft_mesh_square_energy_L1
-- name    : AvramDividend.Classical.avram_b23_original_compact_preleft_mesh_square_energy_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:57:26.841269+00:00
-- url     : https://prove2.me/theorems/659cb80a-080d-4b86-a23b-72e0a572d417
-- title:
--   Original Lévy compact pre-left finite mesh physical square energy integrable on each local event
-- statement:
--   For the physical original spectrally negative Lévy process and controlled pre-left reserve, every finite mesh whose drift-centred source displacements remain inside a compact band has integrable quadratic energy on any localisation event, provided the energy is measurable there. No global second moment of negative marks is postulated.
-- source:
--   Avram-Palmowski-Pistorius (2007), Proposition 4(i), compact stopped Itô-Meyer localisation, used with original physical C2 Taylor remainder bdc5159f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b23_original_compact_preleft_mesh_square_energy_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∀ (A : Set Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0),
      let z : Ω → ℕ → ℝ := fun ω i =>
        Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) (s i)
      let g : Ω → ℕ → ℝ := fun ω i =>
        X.X (t i) ω - X.X (s i) ω - ((t i - s i) : ℝ) * X.c
      let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
      (∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
        z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b) →
      AEStronglyMeasurable Q (P.restrict A) →
      IntegrableOn Q A P := by sorry
