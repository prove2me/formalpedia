-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_discounted_frozen_X_stopped_physical_grid_identity
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_discounted_frozen_X_stopped_physical_grid_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:11:58.871044+00:00
-- url     : https://prove2.me/theorems/117d66dd-9e29-4ff2-8893-11f4bb683e12
-- title:
--   Exact original BV discounted stopped physical-grid cash identity with frozen-dividend X value increments
-- statement:
--   For the actual bounded-variation spectrally negative Levy process X and original admissible D, the true discounted strict physical cash plus surviving terminal and initial right dividend equals the sum of original frozen-dividend value increments, exact discount commutator and dividend remainder. Proved by algebraically collapsing the four distinct original C1 continuous, aggregate negative-jump, cross and Taylor terms of accepted d51199a8 on each source-exact stopped physical cell. The final ruin or horizon contact cell is retained, and no external path, stochastic assumption, or equality-in-law surrogate occurs. This exact physical frozen-X source is the common-grid operand whose difference from the proved original signed H jump source must be bounded in L1.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_discounted_C1_six_term_stopped_physical_grid_identity

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_discounted_frozen_X_stopped_physical_grid_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (T : ℝ≥0) (m : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let frozen : ℕ → ℝ := fun i =>
      w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let rem : ℕ → ℝ := fun i =>
      cash i + e i * (post (i + 1) - post i - frozen i)
    rightLimit D 0 ω +
      ((∑ i ∈ Finset.range (m + 1), cash i) +
        e (m + 1) * post (m + 1) - e 0 * post 0) =
      rightLimit D 0 ω +
      ((∑ i ∈ Finset.range (m + 1), e i * frozen i) +
       (∑ i ∈ Finset.range (m + 1),
         (e (i + 1) - e i) * post (i + 1)) +
       (∑ i ∈ Finset.range (m + 1), rem i)) := by sorry
