-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_global_C1_Taylor_error_le_BV_source_mass
-- name    : AvramDividend.Classical.avram_bv_error7_original_global_C1_Taylor_error_le_BV_source_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:34:45.116327+00:00
-- url     : https://prove2.me/theorems/12895109-9e0a-455c-b5af-3e5a94510b3b
-- title:
--   Global original BV discounted physical-grid C1 Taylor error bounded by intrinsic source variation mass
-- statement:
--   For the genuine bounded-variation spectrally negative Lévy process X, original admissible dividends D and every physical monotone grid 0..T, if the entire pre-right-payment reserve segment of every cell stays in one compact interior band on which w has a common Lipschitz constant L and |deriv w|≤L, then the exact original discounted C1 Taylor source error is bounded uniformly by 2L times |X.drift|T+|T X.drift-X_T|. This is true for coarse as well as fine actual cells and supplies the missing global uniform integrability envelope for physical-grid positive-error convergence, with no BV prebudget or surrogate process.
-- source:
--   Original process BV Y variation bound b473d1e9-c7cd-404f-950e-d1cc9dca5900 Proved; compact Taylor deterministic analytic child avram_bv_error7_compact_Taylor_cell_bound_of_lipschitz_and_deriv (authoring job a286be42-8473-4f16-a884-77c21f259eb4). For T≤1 the envelope is integrable by 09287ead-652a-4521-8a54-ac198d1c917b. This theorem does not yet remove the compact-band restriction on stopped contact/cap cells.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_Y_grid_variation_le_integrable_source_mass
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_global_C1_Taylor_error_le_BV_source_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (a b L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      |w z - w y| ≤ L * |z - y|)
    (hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ L)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
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
       |∑ i ∈ Finset.range n,
          Real.exp (-(q * (u i : ℝ))) *
            (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
         (2 * L) * (|X.drift| * (T : ℝ) +
           |(T : ℝ) * X.drift - X.X T ω|)) := by sorry
