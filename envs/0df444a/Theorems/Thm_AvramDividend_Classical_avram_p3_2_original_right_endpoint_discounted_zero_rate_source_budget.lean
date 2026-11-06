-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_right_endpoint_discounted_zero_rate_source_budget
-- name    : AvramDividend.Classical.avram_p3_2_original_right_endpoint_discounted_zero_rate_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:53:16.572198+00:00
-- url     : https://prove2.me/theorems/f2a14010-702e-454d-8b5c-f574a9ddf491
-- title:
--   Original BV right-endpoint once-discounted physical stopped source
-- statement:
--   At each strict original stopped BV grid prefix, right-endpoint discounting of unweighted physical dividendMeasure cash and original pre-rightpayment terminal is bounded by w(x), discounted physical V source increments and exact discrete discount drift correction. The cash has only one discount and the source uses actual X and D.
-- source:
--   Specialise Proved avram_p3_grid3_original_stopped_strict_prefix_zero_atom_budget at cash rate zero and weights r j = exp(-q * u j). Show r0=1 and all r nonnegative; simplify the zero-rate ENNReal integrand exactly.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_stopped_strict_prefix_zero_atom_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_right_endpoint_discounted_zero_rate_source_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (m n : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let r : ℕ → ℝ := fun j => Real.exp (-(q * (u j : ℝ)))
    u n < τ →
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let cash0 : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        (1 : ℝ≥0∞) ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    rightLimit D 0 ω +
      (∑ i ∈ Finset.range n, r (i + 1) * cash0 i) +
        r n * post n ≤
      w x + (∑ i ∈ Finset.range n, r (i + 1) * source i) +
        ∑ i ∈ Finset.range n, (r (i + 1) - r i) * post i:= by sorry
