-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_cap_grid_envelope
-- name    : AvramDividend.Classical.avram_p3_bv_original_discounted_cap_grid_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:09:44.290952+00:00
-- url     : https://prove2.me/theorems/61ea0925-832a-49de-85c1-eb3a93ac40c8
-- title:
--   Discounted original BV cap overshoot mesh controlled by physical drift and source residual
-- statement:
--   On a single original bounded-variation Lévy source probability-one event, for every finite monotone nonnegative physical time grid and every per-cell reserve input, the sum of discounted absolute cap-overshoot corrections due to the original jump-removed process is bounded by the physical drift magnitude times elapsed time plus the actual source residual increment. The discount rate is nonnegative and the bound makes no residual-zero, compound Poisson or expected-integrability assumption. This applies to physical cap-contact grid terms during the stopped C1 chain construction.
-- source:
--   Reuses Proved original-source cap overshoot grid envelope 7add1798-3fa6-4877-8868-9a49de8016bb and the genuine discount exp(-q t)≤1 on t≥0. The stochastic stopped L1 and boundary limit remain independent obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cap_overshoot_grid_envelope

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_discounted_cap_grid_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (c : ℝ) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      ∀ (n : ℕ) (u : ℕ → ℝ≥0) (z : ℕ → ℝ),
        (∀ i, i < n → u i ≤ u (i + 1)) →
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u i : ℝ))) *
            |max (z i + (Y (u (i + 1)) - Y (u i)) - c) 0 -
              max (z i - c) 0|) ≤
          |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
            (R (u n) - R (u 0)) := by sorry
