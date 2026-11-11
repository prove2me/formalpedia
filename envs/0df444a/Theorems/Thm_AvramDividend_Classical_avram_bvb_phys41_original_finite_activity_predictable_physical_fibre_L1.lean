-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys41_original_finite_activity_predictable_physical_fibre_L1
-- name    : AvramDividend.Classical.avram_bvb_phys41_original_finite_activity_predictable_physical_fibre_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:25:36.7932+00:00
-- url     : https://prove2.me/theorems/4f36ad0c-3d91-4ad2-9882-af601e3c7516
-- title:
--   Finite original predictable negative-mark kernel gives physically integrable nested compensator on a bounded clock
-- statement:
--   On the original sample space with original right-continuous filtration, any predictable negative-mark kernel supported on reserves at most a finite bound and discounted by exp(-qt), with continuous killed-negative value function and finite negative Levy activity, has an integrable full physical-time double compensator integral. Preserve original time, original probability, and full mark space; no first moment of marks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys41_original_finite_activity_predictable_physical_fibre_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (c : ℝ) (hc : 0 ≤ c)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) (T : ℝ≥0)
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ≤ c) :
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
