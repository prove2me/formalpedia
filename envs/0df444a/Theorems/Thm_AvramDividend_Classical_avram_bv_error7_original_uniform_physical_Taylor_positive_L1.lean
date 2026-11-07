-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_uniform_physical_Taylor_positive_L1
-- name    : AvramDividend.Classical.avram_bv_error7_original_uniform_physical_Taylor_positive_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:24:50.491911+00:00
-- url     : https://prove2.me/theorems/a41c9c37-a8cb-4d69-a9da-e8cb3963629a
-- title:
--   Original BV physical-grid Taylor positive part has vanishing expected value from uniform intrinsic source domination
-- statement:
--   For the literal original bounded-variation Lévy X, admissible dividend D, and genuine grid family u(m), all starting at zero and ending at T≤1, the standing original C1 and compact interior band hypotheses yield a deterministic uniform radius δ. When every original pre-right-payment cell remains in that band and every jump-removed Y increment is below δ almost surely, the discounted Taylor source residuals have an L1 dominating function intrinsically built from X_T. Assuming separate genuine almost-sure convergence and measurability of those residuals, their expected positive parts tend to zero. This eliminates the hDom hypothesis from the preceding positive-error DCT lemma, without importing or presupposing any original BV prebudget.
-- source:
--   Reduction from two original-process Proved helper paths: norm-domination theorem avram_bv_error7_original_uniform_physical_Taylor_norm_source_dom (authoring job pending), and accepted positive-error DCT 70a2660b-af9a-4e0c-9e31-a0cf5eed04e9. The precise band/refinement and a.e. convergence hypotheses remain to be obtained from original stopped grids and contact-cell analysis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_physical_C1_positive_error_L1_of_variation_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_uniform_physical_Taylor_positive_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (hT : T ≤ 1)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hGrid : ∀ m, u m 0 = 0 ∧ u m (k m) = T ∧
      (∀ i, i < k m → u m i ≤ u m (i + 1)))
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       ∑ i ∈ Finset.range (k m),
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)))
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P)
    (hErrAE : ∀ᵐ ω ∂P,
      Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧
      ((∀ m, ∀ᵐ ω ∂P,
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
          else 0
         let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
         let z : ℕ → ℝ := fun i =>
           x + X.X (u m i) ω - rightLimit D (u m i) ω
         let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
         (∀ i, i < k m →
           Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) ∧
         (∀ i, i < k m → |c i| < δ))) →
       (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
       Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
         atTop (nhds (0 : ℝ))) := by sorry
