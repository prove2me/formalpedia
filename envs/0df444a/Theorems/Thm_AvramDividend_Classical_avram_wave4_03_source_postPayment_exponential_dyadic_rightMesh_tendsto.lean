-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_exponential_dyadic_rightMesh_tendsto
-- name    : AvramDividend.Classical.avram_wave4_03_source_postPayment_exponential_dyadic_rightMesh_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:27:14.211419+00:00
-- url     : https://prove2.me/theorems/608b8b12-6d86-4087-ab91-e521cb3bb47c
-- title:
--   Original controlled Lévy postpayment discounted exponential converges along genuine right dyadic grids
-- statement:
--   For the original same-path spectrally negative Lévy source and a true left-continuous adapted dividend D, the postpayment controlled exponential at each right dyadic mesh ceiling of s in a positive finite horizon T tends to its time-s value. The proof uses the proved same-path cadlag right continuity of x+X-D_{t+} and exact dyadic ceiling limit; it is a pointwise integrand limit needed for applying Fatou to a full dividend Stieltjes measure, not a stochastic chain rule or expected budget.
-- source:
--   Canonical postPaymentReserve_cadlag_adapted a2763475 and dyadic ceiling horizon limit da8556b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave4_03_source_postPayment_exponential_dyadic_rightMesh_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (ω : Ω) (s T : ℝ≥0)
    (hT : 0 < T) (hs : s ≤ T) :
    Tendsto
      (fun n : ℕ =>
        let k := Nat.ceil (((s / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
        let u := ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
        Real.exp (θ * (x + X.X u ω - rightLimit D u ω) -
          (u : ℝ) * q)) atTop
      (𝓝 (Real.exp (θ * (x + X.X s ω - rightLimit D s ω) -
        (s : ℝ) * q))) := by sorry
