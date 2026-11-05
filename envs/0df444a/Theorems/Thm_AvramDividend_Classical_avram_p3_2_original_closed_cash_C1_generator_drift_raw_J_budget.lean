-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_closed_cash_C1_generator_drift_raw_J_budget
-- name    : AvramDividend.Classical.avram_p3_2_original_closed_cash_C1_generator_drift_raw_J_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:51:36.500689+00:00
-- url     : https://prove2.me/theorems/0f840f2d-688f-4a7d-881e-020c5d11c9cb
-- title:
--   Original BV closed dividend Stieltjes cash bounded by literal C1 HJB drift and raw-J plus shrinking source errors
-- statement:
--   The genuine original stopped bounded-variation X/D physical-grid discounted closed Stieltjes cash plus w-terminal reward is bounded by the starting value, original discount product correction, the literal original generator source drift deriv w(reserve)*Δt*X.drift, true negative-jump w kernel, and two explicitly retained C1 Taylor/mixed raw-J errors. Source identity derives from the accepted original cash inequality 7266a3c5 and the exact closed-cap V drift derivative split; it treats strict preruin, initial grid cell, cap and original rightLimit D without a surrogate source. The remaining original Taylor/mixed errors are independently shown to vanish on strict compact physical refining grids.
-- source:
--   Accepted original capped cash/commutator 7266a3c5 and exact V drift C1 remainder lemma, original admissibility cap closure; no further assumptions beyond explicit pre-ruin and cap-safe grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_closed_cash_interior_w_commutator_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_caplinear_drift_cell_C1_derivative_remainder_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postrightpayment_reserve_closed_cap

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_closed_cash_C1_generator_drift_raw_J_budget
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
      (∀ i : ℕ, i < n →
        C = ⊤ ∨ x + X.X (u i) ω - rightLimit D (u i) ω +
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) ≤ C.toReal) →
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
        (((∑ i ∈ Finset.range n,
          E (u i) * (deriv w (z i) * c i)) +
          (∑ i ∈ Finset.range n,
            E (u i) * (w (z i + c i) - w (z i) - deriv w (z i) * c i))) +
         (∑ i ∈ Finset.range n,
          E (u i) * (w (z i - j i) - w (z i))) +
         (∑ i ∈ Finset.range n,
          E (u i) * (w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i)))) := by sorry
