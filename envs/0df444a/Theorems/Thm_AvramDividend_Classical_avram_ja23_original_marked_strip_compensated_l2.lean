-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja23_original_marked_strip_compensated_l2
-- name    : AvramDividend.Classical.avram_ja23_original_marked_strip_compensated_l2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:37:05.78326+00:00
-- url     : https://prove2.me/theorems/924b87ab-e5c3-40ea-86d3-a484d7d0cfd8
-- title:
--   Original finite negative marked strip compensated L2 isometry
-- statement:
--   On the original Levy probability space, show the compensated signed jump mark integral over a fixed finite negative annulus is square-integrable with exact T times the Levy z-squared energy. This is the source Poisson second-moment calculation only, with no Gaussian residual, filtration transfer or limiting operation.
-- source:
--   J-A23 corrected physical source of the Gaussian cutoff difference variance; direct child of 9a1c9ee4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja23_original_marked_strip_compensated_l2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      let S : Set ℝ :=
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let C : Ω → ℝ := fun ω =>
        (∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω) -
          (t : ℝ) * (∫ z in S, z ∂X.ν)
      Integrable (fun ω => (C ω) ^ 2) P ∧
      (∫ ω, (C ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν) := by sorry
