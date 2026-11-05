-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_localised_discounted_C1_mesh_error
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_localised_discounted_C1_mesh_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:22:09.639371+00:00
-- url     : https://prove2.me/theorems/3626dc6a-cd9d-4d73-b2ae-7efb24bde819
-- title:
--   Actual original BV discounted C1 source mesh error bound and localised limit
-- statement:
--   On the actual original bounded-variation Lévy source and an admissible left-continuous dividend strategy, pathwise grids with the same localising endpoint yield an explicit uniform discounted C1 error estimate. Its bound uses the physical drift, genuine original negative-jump sum, and drift-minus-residual BV variation, with actual source-frozen postpayment states. Under local Taylor and finite/remaining jump-tail control, the error converges to zero. The stopping/compact-strip and jump-tail hypotheses remain visible for P3-G/F to discharge; no compensation, HJB sign or stopped chain inequality is assumed.
-- source:
--   The Proved original P-full physical BV jump-removed grid variation theorem and finite-grid two-stage nonlinear C1 bound, combined with the Proved two-stage mesh-error limit; all path functions use the original X.X, original jump sum, and actual rightLimit D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_grid_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_finite_grid_C1_two_stage_error
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_two_stage_mesh_error_limit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_localised_discounted_C1_mesh_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (n : ℕ → ℕ)
    (u : Ω → ℕ → ℕ → ℝ≥0)
    (S : Ω → ℕ → Finset ℕ)
    (hGrid : ∀ ω k i, i < n k → u ω k i ≤ u ω k (i + 1))
    (hZero : ∀ ω k, u ω k 0 = 0)
    (hEnd : ∀ ω k, u ω k (n k) = τ ω) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let c : ℕ → ℕ → ℝ := fun k i =>
        Y (u ω k (i + 1)) - Y (u ω k i)
      let j : ℕ → ℕ → ℝ := fun k i =>
        J (u ω k (i + 1)) - J (u ω k i)
      let d : ℕ → ℕ → ℝ := fun k i =>
        X.X (u ω k (i + 1)) ω - X.X (u ω k i) ω
      let z : ℕ → ℕ → ℝ := fun k i =>
        x + X.X (u ω k i) ω - rightLimit D (u ω k i) ω
      let e : ℕ → ℕ → ℝ := fun k i =>
        Real.exp (-(q * (u ω k i : ℝ)))
      let tail : ℕ → ℝ := fun k =>
        ∑ i ∈ Finset.range (n k),
          if i ∈ S ω k then |c k i| else |j k i|
      let err : ℕ → ℝ := fun k =>
        ∑ i ∈ Finset.range (n k),
          e k i * ((w (z k i + d k i) - w (z k i)) -
            (w (z k i - j k i) - w (z k i)) -
            deriv w (z k i) * c k i)
      let B : ℝ := |X.drift| * (τ ω : ℝ) + (R (τ ω) - R 0)
      ∀ (ε : ℕ → ℝ) (K : ℝ),
        (∀ k, 0 ≤ ε k) → 0 ≤ K →
        (∀ k i, i < n k →
          |w (z k i + c k i) - w (z k i) -
            deriv w (z k i) * c k i| ≤ ε k * |c k i|) →
        (∀ k i, i < n k → i ∈ S ω k →
          |w (z k i + c k i - j k i) - w (z k i - j k i)| ≤
              K * |c k i| ∧
          |w (z k i + c k i) - w (z k i)| ≤ K * |c k i|) →
        (∀ k i, i < n k → i ∉ S ω k →
          |w (z k i + c k i - j k i) - w (z k i + c k i)| ≤
              K * |j k i| ∧
          |w (z k i - j k i) - w (z k i)| ≤ K * |j k i|) →
        Filter.Tendsto ε Filter.atTop (nhds 0) →
        Filter.Tendsto tail Filter.atTop (nhds 0) →
        (∀ k, |err k| ≤ ε k * B + 2 * K * tail k) ∧
          Filter.Tendsto err Filter.atTop (nhds 0) := by sorry
