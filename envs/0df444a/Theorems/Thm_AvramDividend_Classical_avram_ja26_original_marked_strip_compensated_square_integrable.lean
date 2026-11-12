-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja26_original_marked_strip_compensated_square_integrable
-- name    : AvramDividend.Classical.avram_ja26_original_marked_strip_compensated_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:00:55.611234+00:00
-- url     : https://prove2.me/theorems/991a7eca-ccb4-417d-9ae1-402de2198ff9
-- title:
--   Original finite marked-strip compensated square integrability from all-negative count L2
-- statement:
--   Under the original finite-activity standing assumptions, the signed compensated stochastic jump sum with marks in a fixed negative finite strip is square-integrable. Prove via original finite negative jump count quadratic integrability, bounded marks and compensation. Keep the actual original probability space, filtration and physical jump measure.
-- source:
--   J-A26 branch: integrability half of original marked-strip compensated L2 isometry 924b87ab; companion exact moment identity ec5fe7b6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja26_original_marked_strip_compensated_square_integrable
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
      Integrable (fun ω => (C ω) ^ 2) P := by sorry
