-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja25_original_marked_strip_square_integrable
-- name    : AvramDividend.Classical.avram_ja25_original_marked_strip_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:59:34.573212+00:00
-- url     : https://prove2.me/theorems/85768b34-a053-4859-aa9b-f5f00605d537
-- title:
--   Finite activity makes the exact original compensated marked strip square integrable
-- statement:
--   On the original probability space, the finite marked jump strip between two negative cutoffs is the difference of two actual compensated small-band integrals. Both are square-integrable under finite negative jump activity, so their difference is square-integrable. The source-exact signed strip equality is already Proved; no mark covariance or Brownian representation is claimed.
-- source:
--   Proved original physical strip equality fe464249, finite cutoff L2 f36bf9b5, small-band adaptedness 7ba6e5dc, generic square sum integrability d3782c63. Direct source-faithful prerequisite to 924b87ab.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja25_original_marked_strip_square_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
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
