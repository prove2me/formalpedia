-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_interior_Taylor_error_le_L1_source_mass
-- name    : AvramDividend.Classical.avram_bv_error7_original_interior_Taylor_error_le_L1_source_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:59:36.858914+00:00
-- url     : https://prove2.me/theorems/d7008b37-9222-40a4-9996-ee5566919641
-- title:
--   Original stopped compact-interior discounted C1 Taylor error bounded by integrable physical source mass
-- statement:
--   On an event of full original probability, for any BV X and admissible original dividend D, the exact discounted C1 Taylor error of genuine jump-removed Y cells in a compact positive subcap band is bounded by epsilon times |drift| T + |T drift-X_T| whenever their true source Y increments fall below a common deterministic C1 threshold. This combines the Proved original physical C1 Taylor sum estimate with BV-ERROR7's stronger source variation envelope, uniformly over sample-dependent physical grids. The right-hand side is integrable for T≤1 under Standing, as proved by the separate BV-ERROR7 first-moment child. Cap/ruin/contact cells are explicitly excluded from the interior-band premise and remain to be handled.
-- source:
--   Proved original discounted C1 mesh bound 23921613-c6f7-426c-a634-d2ddcd457e42. Genuine original BV Y variation child b473d1e9-c7cd-404f-950e-d1cc9dca5900. Integral envelope child 09287ead-652a-4521-8a54-ac198d1c917b. No Open canonical BV prebudget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_C1_physical_mesh_error_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_interior_Taylor_error_le_L1_source_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
          u 0 = 0 → u n = T →
          (∀ i, i < n → u i ≤ u (i + 1)) →
          (let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
            else 0
           let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
           let z : ℕ → ℝ := fun i =>
             x + X.X (u i) ω - rightLimit D (u i) ω
           let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
           (∀ i, i < n →
             Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
           (∀ i, i < n → |c i| < δ) →
           |∑ i ∈ Finset.range n,
             Real.exp (-(q * (u i : ℝ))) *
               (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
             ε * (|X.drift| * (T : ℝ) +
               |(T : ℝ) * X.drift - X.X T ω|)) := by sorry
