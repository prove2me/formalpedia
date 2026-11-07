-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_generator_and_drift_cells_integrable_sum
-- name    : AvramDividend.Classical.avram_p3_grid4_original_generator_and_drift_cells_integrable_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:43:57.050884+00:00
-- url     : https://prove2.me/theorems/14b432c6-18c9-46b1-aa2b-08ef65913e71
-- title:
--   Per-cell L1 bounds give integrability of the original stopped BV generator plus drift sum
-- statement:
--   Separates the integrability of the actual original signed physical grid B into two concrete and independently provable classes of source-exact cell integrability obligations, the stopped HJB generator cell and raw BV residual cell. Finite-sum integrability then follows, giving the missing B_n L1 aggregation in witness 2bc848f9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_generator_and_drift_cells_integrable_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) :
    let G : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ ENNReal.ofReal Z < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w Z - q * w Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ ENNReal.ofReal Z < C then
        Real.exp (-(q * (u n i : ℝ))) * deriv w Z
       else 0) * (R (u n i) - R (u n (i + 1)))
    (∀ n i, i < n + 1 → Integrable (G n i) P) →
    (∀ n i, i < n + 1 → Integrable (H n i) P) →
    ∀ n, Integrable (fun ω =>
      (∑ i ∈ Finset.range (n + 1), G n i ω) +
      (∑ i ∈ Finset.range (n + 1), H n i ω)) P := by sorry
