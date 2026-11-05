-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_closed_cash_generator_budget_up_to_mesh_epsilon
-- name    : AvramDividend.Classical.avram_p3_2_original_stopped_closed_cash_generator_budget_up_to_mesh_epsilon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T01:12:23.326373+00:00
-- url     : https://prove2.me/theorems/317d835e-a9d5-4e79-b160-8ba2c029cd94
-- title:
--   Original stopped closed dividend cash bounded by actual generator drift and raw-J up to vanishing mesh error
-- statement:
--   For actual controlled original bounded-variation Lévy source X/D on strict compact pre-ruin refining physical grids, the exact discounted closed Stieltjes dividend cash plus genuine terminal w is bounded by w(x), original discount-clock correction, literal generator pure drift and raw negative-J w increments, up to any prescribed positive mesh error for all sufficiently fine grids. This composes the Proved source closed cash 0f840f2d, simultaneous C1 Taylor/mixed-J vanishing 8442e7aa, automatic original compact cap safety 03bf0d45, and actual raw-cell cumulative-J equality 7f6c3677. It still requires an original jump compensator and HJB expectation bridge; no circular canonical theorem, auxiliary process or omitted cap-contact premise.
-- source:
--   Accepted actual original X/D source results 0f840f2d,8442e7aa,03bf0d45,7f6c3677; stop clocks and strict compact cap conditions retained explicitly.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_closed_cash_C1_generator_drift_raw_J_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_source_C1_two_errors_joint_mesh_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_compact_reserve_band_implies_cap_safe_drift
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_raw_cell_eq_cumulative_J_increment

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_stopped_closed_cash_generator_budget_up_to_mesh_epsilon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_open : IsOpen {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hb : C = ⊤ ∨ b < C.toReal)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      ∀ (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ),
        let Y : ℝ≥0 → ℝ := fun t =>
          x + X.X t ω - rightLimit D t ω
        let z : ℕ → ℕ → ℝ := fun m i => Y (u m i)
        let c : ℕ → ℕ → ℝ := fun m i =>
          ((u m (i + 1) : ℝ) - (u m i : ℝ)) * X.drift
        let j : ℕ → ℕ → ℝ := fun m i =>
          J (u m (i + 1)) - J (u m i)
        (∀ m, Monotone (u m)) →
        (∀ m, u m 0 = 0) →
        (∀ m, u m (n m) = T) →
        (∀ m i, i < n m →
          u m (i + 1) = 0 ∨
          (u m (i + 1) : ℝ≥0∞) < ruinTime X x D ω) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
            (u m (i + 1) : ℝ) - (u m i : ℝ) < δ) →
        (∀ m i, i < n m → z m i ≤ b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i - j m i) (z m i) ⊆ Set.Icc a b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i + c m i - j m i)
            (z m i + c m i) ⊆ Set.Icc a b) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop,
            E T * w (Y T) +
              (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
                ENNReal.ofReal (Real.exp (-(q * s)))
                  ∂(dividendMeasure D ω)).toReal ≤
            w x +
              (∑ i ∈ Finset.range (n m),
                (E (u m (i + 1)) - E (u m i)) *
                  V (Y (u m (i + 1)))) +
              (∑ i ∈ Finset.range (n m),
                E (u m i) * (deriv w (z m i) * c m i)) +
              (∑ i ∈ Finset.range (n m),
                E (u m i) * (w (z m i - j m i) - w (z m i))) + η := by sorry
