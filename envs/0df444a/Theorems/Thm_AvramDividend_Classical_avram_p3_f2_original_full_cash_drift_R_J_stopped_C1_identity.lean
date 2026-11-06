-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_full_cash_drift_R_J_stopped_C1_identity
-- name    : AvramDividend.Classical.avram_p3_f2_original_full_cash_drift_R_J_stopped_C1_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:37:59.103244+00:00
-- url     : https://prove2.me/theorems/3e11dc25-aad1-4fac-92e2-4e306db375b3
-- title:
--   Original stopped discounted Stieltjes cash C1 identity in drift, residual R and raw negative-jump terms
-- statement:
--   The original exact stopped Stieltjes dividend-cash telescoping identity is rewritten source-faithfully with the actual Lévy drift and original residual BV R increments replacing the jump-removed Y derivative sum. This preserves explicit negative-jump Taylor generator contribution, the non-linear commutator and Taylor errors, discount differences, horizon endpoint values and exact finite-mesh dividend remainder.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_full_cash_Y_J_C1_commutator_identity
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_Y_drift_minus_R_physical_grid
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_full_cash_drift_R_J_stopped_C1_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Set.Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let frozen : ℕ → ℝ := fun i =>
      w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let rem : ℕ → ℝ := fun i =>
      cash i + e i * (post (i + 1) - post i - frozen i)
    (∑ i ∈ Finset.range n, cash i) + e n * post n - e 0 * post 0 =
      ((∑ i ∈ Finset.range n,
        e i * (deriv w (z i) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) -
       (∑ i ∈ Finset.range n,
        e i * (deriv w (z i) * (R (u (i + 1)) - R (u i))))) +
      (∑ i ∈ Finset.range n, e i * (w (z i - j i) - w (z i))) +
      (∑ i ∈ Finset.range n, e i * (w (z i + c i - j i) - w (z i + c i) - w (z i - j i) + w (z i))) +
      (∑ i ∈ Finset.range n, e i * (w (z i + c i) - w (z i) - deriv w (z i) * c i)) +
      (∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1)) +
      (∑ i ∈ Finset.range n, rem i) := by sorry
