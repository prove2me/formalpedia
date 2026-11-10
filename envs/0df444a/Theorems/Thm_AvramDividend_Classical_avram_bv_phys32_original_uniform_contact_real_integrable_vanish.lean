-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys32_original_uniform_contact_real_integrable_vanish
-- name    : AvramDividend.Classical.avram_bv_phys32_original_uniform_contact_real_integrable_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:15:20.016203+00:00
-- url     : https://prove2.me/theorems/dc469ad3-b865-48e4-9db6-5280a2240399
-- title:
--   Original uniform BV finite-activity collision/contact error is integrable as a real variable and vanishes in expected value
-- statement:
--   For the same original BV X and exact uniform u, the real-valued positive original jump-collision plus occupied-width error is Integrable at every mesh index and has expected value converging to zero. This transports Proved original fullmark finite rate, original count/physical occupancy measurability, and source-exact joint ENNReal mass theorem ea57e6f2 into real-valued L1 control required for the ErrContact component of root-connected finite-activity BV physical ledger child 6a6dda41. No artificial grid or separate global B L1.
-- source:
--   Needed by finite-cap physical stopped cash/contact witness 6a6dda41, ultimately 2bc848f9 → 4f605d76.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys32_original_uniform_contact_real_integrable_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      (T : ℝ) * (i : ℝ) / ((n : ℝ) + 2)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ))
    let K : ℕ → Ω → ℝ≥0∞ := fun n ω =>
      ∑ i ∈ Finset.range (n + 2),
        if X.X (u n (i + 1)) ω - X.X (u n i) ω <
          X.drift * (((u n (i + 1) - u n i : ℝ≥0) : ℝ))
        then (1 : ℝ≥0∞) else 0
    let Err : ℕ → Ω → ℝ := fun n ω =>
      (N ω - K n ω + (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * N ω).toReal
    (∀ n, Integrable (Err n) P) ∧
      Filter.Tendsto (fun n => ∫ ω, Err n ω ∂P)
        Filter.atTop (nhds (0 : ℝ)) := by sorry
