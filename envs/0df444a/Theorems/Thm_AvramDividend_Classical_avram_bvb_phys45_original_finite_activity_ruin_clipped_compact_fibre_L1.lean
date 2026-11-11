-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys45_original_finite_activity_ruin_clipped_compact_fibre_L1
-- name    : AvramDividend.Classical.avram_bvb_phys45_original_finite_activity_ruin_clipped_compact_fibre_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:17:00.747383+00:00
-- url     : https://prove2.me/theorems/a6f09097-401f-4600-8066-7602cd4f1140
-- title:
--   Original bounded-clock ruin-clipped compact reserve negative-mark compensator is L1
-- statement:
--   On the original probability space and original right-continuous predictable filtration, take the natural clock clipped by first ruin and a deterministic finite horizon. On its stopped compact prepayment-reserve band [a,b] with a>=0, the physically nested discounted negative-Levy-mark compensation is integrable under finite negative jump activity. This bridges the original stopped predictable compact-band theorem and the same-space physical Fubini kernel result. Includes the first ruin-causing mark and zero reserve when a=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys45_original_finite_activity_ruin_clipped_compact_fibre_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    Integrable (fun ω => ∫ t, ∫ z, H ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by sorry
