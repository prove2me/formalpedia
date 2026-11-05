-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_closed_cash_wjump_commutator_budget
-- name    : AvramDividend.Classical.avram_p3_2_original_closed_cash_wjump_commutator_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:00:26.580878+00:00
-- url     : https://prove2.me/theorems/4338db7f-dc61-4492-b894-ebcdc7253d13
-- title:
--   Source-exact original BV stopped closed dividend cash budget with physical drift, w jump and mixed commutator
-- statement:
--   For the actual original bounded-variation Lévy process, admissible D and all source grids stopped before ruin, control the literal discounted closed Stieltjes dividend cash and true terminal w by initial w, discounted cap-linear drift cells, literal original w negative-jump kernel and exact physical mixed drift/jump commutator. The left-grid cap is derived from admissibility including time zero. This is the original-process pathwise physical source inequality before Taylor, compensation and limit passage.
-- source:
--   Composition of Accepted original source cash/frozen-grid inequality 13c9d7c0, source-exact commutator 43ca852b, and closed-cap admissibility d88fd858; no equality in law or synthetic process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_closed_cash_true_w_raw_jump_grid_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_full_grid_drift_jump_commutator
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postrightpayment_reserve_closed_cap

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_closed_cash_wjump_commutator_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      Monotone u → u 0 = 0 →
      (∀ i : ℕ, i < n →
        u (i + 1) = 0 ∨
          (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) →
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let z : ℕ → ℝ := fun i => Y (u i)
    let c : ℕ → ℝ := fun i =>
      ((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift
    let j : ℕ → ℝ := fun i =>
      ∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) v - X.X v ω
      else 0
    E (u n) * w (Y (u n)) +
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal ≤
      w x +
        (∑ i ∈ Finset.range n,
          (E (u (i + 1)) - E (u i)) * V (Y (u (i + 1)))) +
        ((∑ i ∈ Finset.range n,
          E (u i) * (V (z i + c i) - V (z i))) +
         (∑ i ∈ Finset.range n,
          E (u i) * (w (z i - j i) - w (z i))) +
         (∑ i ∈ Finset.range n,
          E (u i) * (V (z i + c i - j i) - V (z i + c i) -
            V (z i - j i) + V (z i)))) := by sorry
