-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_true_physical_Taylor_error_positive_L1_concrete
-- name    : AvramDividend.Classical.avram_bv_error7_original_true_physical_Taylor_error_positive_L1_concrete
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:25:18.231199+00:00
-- url     : https://prove2.me/theorems/d371124e-4679-4f0b-b3a6-edf76ad723fe
-- title:
--   Concrete original BV stopped-grid Taylor positive error is L1 and vanishes in expectation
-- statement:
--   For the genuine bounded-variation Lévy process X and original admissible dividend strategy D, the exact true stopped physical-grid C1 Taylor error is given literally as an expression in the conclusion. Under compact interior C1 band and vanishing mesh conditions, its positive part is integrable and its expectation tends to zero. No separate Err witness, assumed error measurability, BV prebudget or invented process is used.
-- source:
--   Concrete instantiation of previously proved original true-prefix positive-L1 theorem with exact J, Y, X, D cell expression.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_random_stopped_physical_C1_true_positive_error_L1
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_true_physical_Taylor_error_positive_L1_concrete
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hwMeas : Measurable w)
    (hDerivMeas : Measurable (deriv w))
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      |w z - w y| ≤ L * |z - y|)
    (hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ L)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (hT : T ≤ 1)
    (u : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ)
    (k : ℕ → Ω → ℕ) (hk : ∀ m, Measurable (k m))
    (hBound : ∀ m ω, k m ω ≤ N m)
    (hGrid : ∀ m ω, u m 0 = 0 ∧ u m (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m i ≤ u m (i + 1)))
    (hPath : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℕ → ℝ := fun m i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℕ → ℝ := fun m i =>
         Y (u m (i + 1)) - Y (u m i)
       (∀ m i, i < k m ω →
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) ∧
       (∀ δ : ℝ, 0 < δ →
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m ω → |c m i| < δ))) :
    let Err : ℕ → Ω → ℝ := fun m ω =>
          (let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
            else 0
           let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
           let z : ℕ → ℝ := fun i =>
             x + X.X (u m i) ω - rightLimit D (u m i) ω
           let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
           ∑ i ∈ Finset.range (k m ω),
             Real.exp (-(q * (u m i : ℝ))) *
               (w (z i + c i) - w (z i) - deriv w (z i) * c i));
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
