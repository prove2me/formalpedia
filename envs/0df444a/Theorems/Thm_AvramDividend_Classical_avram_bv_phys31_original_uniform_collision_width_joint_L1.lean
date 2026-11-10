-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys31_original_uniform_collision_width_joint_L1
-- name    : AvramDividend.Classical.avram_bv_phys31_original_uniform_collision_width_joint_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:12:19.063266+00:00
-- url     : https://prove2.me/theorems/ea57e6f2-e0b8-4ca3-ae7a-7b4dbb9c2078
-- title:
--   Actual uniform BV physical grid has jointly vanishing jump-collision and occupied-width L1 error
-- statement:
--   For the exact original finite-activity BV uniform grid u_n i = Ti/(n+2) reaching T at n+2, the full-horizon negative jump collision excess plus mesh width times genuine source fullmark count has expected mass tending to zero. This combines authoritative Proved 5962720e (full uniform collision) and Proved fbf40631 (uniform occupied width), retaining same original X, T and u. It is necessary contact-error support of finite-cap original stopped physical ledger child 6a6dda41.
-- source:
--   Root-connected original physical ledger finite-activity source e6a0b83b → c5ce01c6 → 2bc848f9 → 4f605d76; source exact grid, no arbitrary grid assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys31_original_uniform_collision_width_joint_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      (T : ℝ) * (i : ℝ) / ((n : ℝ) + 2)) :
    Filter.Tendsto (fun n : ℕ => ∫⁻ ω,
      (((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) -
        (∑ i ∈ Finset.range (n + 2),
          if X.X (u n (i + 1)) ω - X.X (u n i) ω <
            X.drift * (((u n (i + 1) - u n i : ℝ≥0) : ℝ))
          then (1 : ℝ≥0∞) else 0)) +
        (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) *
          ((Measure.count.restrict {t : ℝ≥0 |
            0 < t ∧ X.X t ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0}).map
            (fun t : ℝ≥0 => (t, X.X t ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))
            (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
