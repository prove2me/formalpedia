-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise36_original_dyadic_physical_L1_source
-- name    : AvramDividend.Classical.avram_anoise36_original_dyadic_physical_L1_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:09:32.192017+00:00
-- url     : https://prove2.me/theorems/ebfd1029-08bb-41db-a52b-6b115e404261
-- title:
--   Original finite-activity dyadic signed jump source converges with integrable domination
-- statement:
--   For the same original marked jump process and original Levy intensity, the dyadic signed finite-step approximation converges almost surely to the original compensated finite-band future increment. A single integrable function dominates all dyadic terms. The proof uses the actual negative count quadratic bound, disjoint dyadic cell partition, and deterministic at-most-cell-width signed mark error. No Brownian identification or large-mark first moment is introduced.
-- source:
--   Physical half of root-connected Open 4da238cd, paired with anoise35's original-filtration conditional centring. This isolates the source-measure approximation from martingale/filter arguments without changing the original dyadic M or target value.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise36_original_dyadic_physical_L1_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ T : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C k i)
      let M : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((J k i ω).toReal -
              (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
      ∃ bound : Ω → ℝ, Integrable bound P ∧
        (∀ᵐ ω ∂P, Tendsto (fun k => M k ω) atTop
          (𝓝 (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω))) ∧
        (∀ k, ∀ᵐ ω ∂P, ‖M k ω‖ ≤ bound ω) := by sorry
